use super::{Error, Item, Span, Value, ValueKind};
use crate::*;
use anyhow::Result;
use std::collections::{hash_map::Entry, HashMap, HashSet};

#[derive(Default)]
pub struct Resolver {
    name_lookup: HashMap<String, Definition>,
    types: Arena<TypeDef>,
    types_copied: HashMap<(String, TypeId), TypeId>,
    anon_types: HashMap<Key, TypeId>,
    functions: Arena<Function>,
    globals: Arena<Global>,
}

#[derive(PartialEq, Eq, Hash)]
enum Key {
    Variant(Vec<(String, Type)>),
    Record(Vec<(String, Type)>),
    Flags(Vec<String>),
    Tuple(Vec<Type>),
    Enum(Vec<String>),
    List(Type),
    Option(Type),
    Expected(Type, Type),
    Union(Vec<Type>),
    Stream(Type, Type),
}

impl Resolver {
    pub(super) fn resolve(
        mut self,
        name: &str,
        fields: &[Item<'_>],
        deps: &HashMap<String, Interface>,
    ) -> Result<Interface> {
        // First pull in any names from our dependencies
        self.process_use(fields, deps)?;
        // ... then register our own names
        self.register_names(fields)?;

        // With all names registered we can now fully expand and translate all
        // types.
        for field in fields {
            let t = match field {
                Item::TypeDef(t) => t,
                _ => continue,
            };
            if let Definition::Type(id) = self.name_lookup[&*t.name.name] {
                let kind = self.resolve_type_def(&t.ty)?;
                self.types.get_mut(id).unwrap().kind = kind;
            } else {
                unreachable!();
            }
        }

        // And finally we can resolve all type references in functions/globals
        // and additionally validate that types thesmelves are not recursive
        let mut valid_types = HashSet::new();
        let mut visiting = HashSet::new();
        for field in fields {
            match field {
                Item::Value(v) => self.resolve_value(v)?,
                Item::Resource(r) => self.resolve_resource(r)?,
                Item::TypeDef(t) => {
                    if let Definition::Type(ty) = self.name_lookup[&*t.name.name] {
                        self.validate_type_not_recursive(
                            t.name.span,
                            ty,
                            &mut visiting,
                            &mut valid_types,
                        )?;
                    } else {
                        unreachable!();
                    }
                }
                _ => continue,
            }
        }

        Ok(Interface {
            name: name.to_string(),
            module: None,
            name_lookup: self.name_lookup,
            types: self.types,
            functions: self.functions,
            globals: self.globals,
            interface_lookup: Default::default(),
            interfaces: Default::default(),
        })
    }

    fn process_use<'a>(
        &mut self,
        fields: &[Item<'a>],
        deps: &'a HashMap<String, Interface>,
    ) -> Result<()> {
        for field in fields {
            let u = match field {
                Item::Use(u) => u,
                _ => continue,
            };
            let mut dep = &deps[&*u.from[0].name];
            let mut prev = &*u.from[0].name;
            for name in u.from[1..].iter() {
                dep = match dep.interface_lookup.get(&*name.name) {
                    Some(i) => &dep.interfaces[*i],
                    None => {
                        return Err(Error {
                            span: name.span,
                            msg: format!("`{}` not defined in `{}`", name.name, prev),
                        }
                        .into())
                    }
                };
                prev = &*name.name;
            }

            let mod_name = &u.from[0];

            match &u.names {
                Some(names) => {
                    for name in names {
                        let (my_name, span) = match &name.as_ {
                            Some(id) => (&id.name, id.span),
                            None => (&name.name.name, name.name.span),
                        };

                        match dep.name_lookup.get(&*name.name.name) {
                            Some(Definition::Type(id)) => {
                                let ty = self.copy_type_def(&mod_name.name, dep, *id);
                                self.define_type(my_name, span, ty)?;
                            },
                            Some(Definition::Function(_)) => { todo!() },
                            Some(Definition::Global(_)) => { todo!() },
                            None => {
                                return Err(Error {
                                    span: name.name.span,
                                    msg: "name not defined in submodule".to_string(),
                                }
                                .into());
                            }
                        }
                    }
                }
                None => {
                    let mut names = dep.name_lookup.keys().collect::<Vec<_>>();
                    names.sort(); // produce a stable order by which to add names
                    for name in names {
                        let definition = &dep.name_lookup[name];
                        match definition {
                            Definition::Type(id) => {
                                let ty = self.copy_type_def(&mod_name.name, dep, *id);
                                self.define_type(name, mod_name.span, ty)?;
                            },
                            _ => continue
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn copy_type_def(&mut self, dep_name: &str, dep: &Interface, dep_id: TypeId) -> TypeId {
        if let Some(id) = self.types_copied.get(&(dep_name.to_string(), dep_id)) {
            return *id;
        }
        let ty = &dep.types[dep_id];

        let ty = TypeDef {
            docs: ty.docs.clone(),
            name: ty.name.clone(),
            foreign_module: Some(
                ty.foreign_module
                    .clone()
                    .unwrap_or_else(|| dep_name.to_string()),
            ),
            kind: match &ty.kind {
                TypeDefKind::Type(t) => TypeDefKind::Type(self.copy_type(dep_name, dep, *t)),
                TypeDefKind::Record(r) => TypeDefKind::Record(Record {
                    fields: r
                        .fields
                        .iter()
                        .map(|field| Field {
                            docs: field.docs.clone(),
                            name: field.name.clone(),
                            ty: self.copy_type(dep_name, dep, field.ty),
                        })
                        .collect(),
                }),
                TypeDefKind::Flags(f) => TypeDefKind::Flags(f.clone()),
                TypeDefKind::Tuple(t) => TypeDefKind::Tuple(Tuple {
                    types: t
                        .types
                        .iter()
                        .map(|ty| self.copy_type(dep_name, dep, *ty))
                        .collect(),
                }),
                TypeDefKind::Variant(v) => TypeDefKind::Variant(Variant {
                    cases: v
                        .cases
                        .iter()
                        .map(|case| Case {
                            docs: case.docs.clone(),
                            name: case.name.clone(),
                            ty: self.copy_type(dep_name, dep, case.ty),
                        })
                        .collect(),
                }),
                TypeDefKind::Enum(e) => TypeDefKind::Enum(Enum {
                    cases: e.cases.clone(),
                }),
                TypeDefKind::List(t) => TypeDefKind::List(self.copy_type(dep_name, dep, *t)),
                TypeDefKind::Option(t) => TypeDefKind::Option(self.copy_type(dep_name, dep, *t)),
                TypeDefKind::Expected(e) => TypeDefKind::Expected(Expected {
                    ok: self.copy_type(dep_name, dep, e.ok),
                    err: self.copy_type(dep_name, dep, e.err),
                }),
                TypeDefKind::Union(u) => TypeDefKind::Union(Union {
                    cases: u
                        .cases
                        .iter()
                        .map(|c| UnionCase {
                            docs: c.docs.clone(),
                            ty: self.copy_type(dep_name, dep, c.ty),
                        })
                        .collect(),
                }),
                TypeDefKind::Stream(e) => TypeDefKind::Stream(Stream {
                    element: self.copy_type(dep_name, dep, e.element),
                    end: self.copy_type(dep_name, dep, e.end),
                }),
                TypeDefKind::Resource(r) => {
                    let mut new_funcs = HashMap::default();
                    for (f_name, f_id) in r.functions.iter() {
                        let dep_func = &dep.functions[*f_id];
                        let new_id = self.functions.alloc(Function {
                            is_async: dep_func.is_async,
                            docs: dep_func.docs.clone(),
                            name: dep_func.name.clone(),
                            kind: dep_func.kind.clone(),
                            params: dep_func.params.clone(),
                            result: dep_func.result
                        });
                        new_funcs.insert(f_name.clone(), new_id);
                    }
                    TypeDefKind::Resource(Resource { functions: new_funcs })
                },
            },
        };
        let id = self.types.alloc(ty);
        self.types_copied.insert((dep_name.to_string(), dep_id), id);
        id
    }

    fn copy_type(&mut self, dep_name: &str, dep: &Interface, ty: Type) -> Type {
        match ty {
            Type::Id(id) => Type::Id(self.copy_type_def(dep_name, dep, id)),
            other => other,
        }
    }

    fn register_names(&mut self, fields: &[Item<'_>]) -> Result<()> {
        let mut values = HashSet::new();
        for field in fields {
            match field {
                Item::Resource(r) => {
                    let docs = self.docs(&r.docs);
                    let id = self.types.alloc(TypeDef {
                        docs,
                        name: Some(r.name.name.to_string()),
                        kind: TypeDefKind::Resource(Resource::default()),
                        foreign_module: None,
                    });
                    self.define_type(&r.name.name, r.name.span, id)?;
                }
                Item::TypeDef(t) => {
                    let docs = self.docs(&t.docs);
                    let id = self.types.alloc(TypeDef {
                        docs,
                        name: Some(t.name.name.to_string()),
                        // a dummy kind is used for now which will get filled in
                        // later with the actual desired contents.
                        kind: TypeDefKind::List(Type::U8),
                        foreign_module: None,
                    });
                    self.define_type(&t.name.name, t.name.span, id)?;
                }
                Item::Value(f) => {
                    if !values.insert(&f.name.name) { //TODO-Kyle
                        return Err(Error {
                            span: f.name.span,
                            msg: format!("{:?} defined twice", f.name.name),
                        }
                        .into());
                    }
                }
                Item::Use(_) => {}

                Item::Interface(_) => unimplemented!("Interface resolution not supported"),
            }
        }

        Ok(())
    }

    fn define_type(&mut self, name: &str, span: Span, id: TypeId) -> Result<()> {
        match self.name_lookup.entry(name.to_string()) {
            Entry::Occupied(entry) => {
                let prior_def = entry.get().describe();
                let msg = format!(
                    "type {:?} previously defined as a {}",
                    name, prior_def
                );
                Err(Error { span, msg }.into())
            }
            Entry::Vacant(entry) => {
                entry.insert(Definition::Type(id));
                Ok(())
            }
        }
    }

    fn define_function(&mut self, name: &str, span: Span, ) {
        // TODO-Kyle
    }

    fn resolve_type_def(&mut self, ty: &super::Type<'_>) -> Result<TypeDefKind> {
        Ok(match ty {
            super::Type::Unit => TypeDefKind::Type(Type::Unit),
            super::Type::Bool => TypeDefKind::Type(Type::Bool),
            super::Type::U8 => TypeDefKind::Type(Type::U8),
            super::Type::U16 => TypeDefKind::Type(Type::U16),
            super::Type::U32 => TypeDefKind::Type(Type::U32),
            super::Type::U64 => TypeDefKind::Type(Type::U64),
            super::Type::S8 => TypeDefKind::Type(Type::S8),
            super::Type::S16 => TypeDefKind::Type(Type::S16),
            super::Type::S32 => TypeDefKind::Type(Type::S32),
            super::Type::S64 => TypeDefKind::Type(Type::S64),
            super::Type::Float32 => TypeDefKind::Type(Type::Float32),
            super::Type::Float64 => TypeDefKind::Type(Type::Float64),
            super::Type::Char => TypeDefKind::Type(Type::Char),
            super::Type::String => TypeDefKind::Type(Type::String),
            super::Type::Name(name) => {
                let id = match self.name_lookup.get(&*name.name) {
                    Some(Definition::Type(id)) => *id,
                    Some(_) => {
                        return Err(Error {
                            span: name.span,
                            msg: format!("name `{}` does not refer to type", name.name),
                        }
                        .into())
                    }
                    None => {
                        return Err(Error {
                            span: name.span,
                            msg: format!("no type named `{}`", name.name),
                        }
                        .into())
                    }
                };
                TypeDefKind::Type(Type::Id(id))
            }
            super::Type::List(list) => {
                let ty = self.resolve_type(list)?;
                TypeDefKind::List(ty)
            }
            super::Type::Record(record) => {
                let fields = record
                    .fields
                    .iter()
                    .map(|field| {
                        Ok(Field {
                            docs: self.docs(&field.docs),
                            name: field.name.name.to_string(),
                            ty: self.resolve_type(&field.ty)?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                TypeDefKind::Record(Record { fields })
            }
            super::Type::Flags(flags) => {
                let flags = flags
                    .flags
                    .iter()
                    .map(|flag| Flag {
                        docs: self.docs(&flag.docs),
                        name: flag.name.name.to_string(),
                    })
                    .collect::<Vec<_>>();
                TypeDefKind::Flags(Flags { flags })
            }
            super::Type::Tuple(types) => {
                let types = types
                    .iter()
                    .map(|ty| self.resolve_type(ty))
                    .collect::<Result<Vec<_>>>()?;
                TypeDefKind::Tuple(Tuple { types })
            }
            super::Type::Variant(variant) => {
                if variant.cases.is_empty() {
                    return Err(Error {
                        span: variant.span,
                        msg: "empty variant".to_string(),
                    }
                    .into());
                }
                let cases = variant
                    .cases
                    .iter()
                    .map(|case| {
                        Ok(Case {
                            docs: self.docs(&case.docs),
                            name: case.name.name.to_string(),
                            ty: match &case.ty {
                                Some(ty) => self.resolve_type(ty)?,
                                None => Type::Unit,
                            },
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                TypeDefKind::Variant(Variant { cases })
            }
            super::Type::Enum(e) => {
                if e.cases.is_empty() {
                    return Err(Error {
                        span: e.span,
                        msg: "empty enum".to_string(),
                    }
                    .into());
                }
                let cases = e
                    .cases
                    .iter()
                    .map(|case| {
                        Ok(EnumCase {
                            docs: self.docs(&case.docs),
                            name: case.name.name.to_string(),
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                TypeDefKind::Enum(Enum { cases })
            }
            super::Type::Option(ty) => TypeDefKind::Option(self.resolve_type(ty)?),
            super::Type::Expected(e) => TypeDefKind::Expected(Expected {
                ok: self.resolve_type(&e.ok)?,
                err: self.resolve_type(&e.err)?,
            }),
            super::Type::Union(e) => {
                if e.cases.is_empty() {
                    return Err(Error {
                        span: e.span,
                        msg: "empty union".to_string(),
                    }
                    .into());
                }
                let cases = e
                    .cases
                    .iter()
                    .map(|case| {
                        Ok(UnionCase {
                            docs: self.docs(&case.docs),
                            ty: self.resolve_type(&case.ty)?,
                        })
                    })
                    .collect::<Result<Vec<_>>>()?;
                TypeDefKind::Union(Union { cases })
            }
            super::Type::Stream(s) => TypeDefKind::Stream(Stream {
                element: self.resolve_type(&s.element)?,
                end: self.resolve_type(&s.end)?,
            }),
        })
    }

    fn resolve_type(&mut self, ty: &super::Type<'_>) -> Result<Type> {
        let kind = self.resolve_type_def(ty)?;
        Ok(self.anon_type_def(TypeDef {
            kind,
            name: None,
            docs: Docs::default(),
            foreign_module: None,
        }))
    }

    fn anon_type_def(&mut self, ty: TypeDef) -> Type {
        let key = match &ty.kind {
            TypeDefKind::Type(t) => return *t,
            TypeDefKind::Variant(v) => Key::Variant(
                v.cases
                    .iter()
                    .map(|case| (case.name.clone(), case.ty))
                    .collect::<Vec<_>>(),
            ),
            TypeDefKind::Record(r) => Key::Record(
                r.fields
                    .iter()
                    .map(|case| (case.name.clone(), case.ty))
                    .collect::<Vec<_>>(),
            ),
            TypeDefKind::Flags(r) => {
                Key::Flags(r.flags.iter().map(|f| f.name.clone()).collect::<Vec<_>>())
            }
            TypeDefKind::Tuple(t) => Key::Tuple(t.types.clone()),
            TypeDefKind::Enum(r) => {
                Key::Enum(r.cases.iter().map(|f| f.name.clone()).collect::<Vec<_>>())
            }
            TypeDefKind::List(ty) => Key::List(*ty),
            TypeDefKind::Option(t) => Key::Option(*t),
            TypeDefKind::Expected(e) => Key::Expected(e.ok, e.err),
            TypeDefKind::Union(u) => Key::Union(u.cases.iter().map(|c| c.ty).collect()),
            TypeDefKind::Stream(s) => Key::Stream(s.element, s.end),
            TypeDefKind::Resource(_) => todo!(),
        };
        let types = &mut self.types;
        let id = self
            .anon_types
            .entry(key)
            .or_insert_with(|| types.alloc(ty));
        Type::Id(*id)
    }

    fn docs(&mut self, doc: &super::Docs<'_>) -> Docs {
        let mut docs = None;
        for doc in doc.docs.iter() {
            // Comments which are not doc-comments are silently ignored
            if let Some(doc) = doc.strip_prefix("///") {
                let docs = docs.get_or_insert_with(String::new);
                docs.push_str(doc.trim_start_matches('/').trim());
                docs.push('\n');
            } else if let Some(doc) = doc.strip_prefix("/**") {
                let docs = docs.get_or_insert_with(String::new);
                assert!(doc.ends_with("*/"));
                for line in doc[..doc.len() - 2].lines() {
                    docs.push_str(line);
                    docs.push('\n');
                }
            }
        }
        Docs { contents: docs }
    }

    fn resolve_value(&mut self, value: &Value<'_>) -> Result<()> {
        let docs = self.docs(&value.docs);
        match &value.kind {
            ValueKind::Function {
                is_async,
                params,
                result,
            } => {
                let params = params
                    .iter()
                    .map(|(name, ty)| Ok((name.name.to_string(), self.resolve_type(ty)?)))
                    .collect::<Result<_>>()?;
                let result = self.resolve_type(result)?;
                self.functions.alloc(Function {
                    docs,
                    name: value.name.name.to_string(),
                    kind: FunctionKind::Freestanding,
                    params,
                    result,
                    is_async: *is_async,
                });
            }
            ValueKind::Global(ty) => {
                let ty = self.resolve_type(ty)?;
                self.globals.alloc(Global {
                    docs,
                    name: value.name.name.to_string(),
                    ty,
                });
            }
        }
        Ok(())
    }

    fn resolve_resource(&mut self, resource: &super::Resource<'_>) -> Result<()> {
        let mut functions = HashMap::new();
        let id = match self.name_lookup[&*resource.name.name] {
            Definition::Type(id) => id,
            _ => unreachable!()
        };
        for (statik, value) in resource.values.iter() {
            let (is_async, params, result) = match &value.kind {
                ValueKind::Function {
                    is_async,
                    params,
                    result,
                } => (*is_async, params, result),
                ValueKind::Global(_) => {
                    return Err(Error {
                        span: value.name.span,
                        msg: "globals not allowed in resources".to_string(),
                    }
                    .into());
                }
            };
            let docs = self.docs(&value.docs);
            let mut params = params
                .iter()
                .map(|(name, ty)| Ok((name.name.to_string(), self.resolve_type(ty)?)))
                .collect::<Result<Vec<_>>>()?;
            let result = self.resolve_type(result)?;
            let kind = if *statik {
                FunctionKind::Static {
                    resource: id,
                    name: value.name.name.to_string(),
                }
            } else {
                params.insert(0, ("self".to_string(), Type::Id(id)));
                FunctionKind::Method {
                    resource: id,
                    name: value.name.name.to_string(),
                }
            };
            let func_id = self.functions.alloc(Function {
                is_async,
                docs,
                name: format!("{}::{}", resource.name.name, value.name.name),
                kind,
                params,
                result,
            });
            let func_entry = functions.entry(value.name.name.to_string());
            match func_entry {
                Entry::Occupied(_) => {
                    return Err(Error {
                        span: value.name.span,
                        msg: format!("{:?} defined twice in this resource", value.name.name),
                    }
                    .into());
                },
                Entry::Vacant(entry) => entry.insert(func_id),
            };
        }
        let resource_entry = match &mut self.types[id].kind {
            TypeDefKind::Resource(r) => r,
            _ => unreachable!()
        };
        resource_entry.functions = functions;
        Ok(())
    }

    fn validate_type_not_recursive(
        &self,
        span: Span,
        ty: TypeId,
        visiting: &mut HashSet<TypeId>,
        valid: &mut HashSet<TypeId>,
    ) -> Result<()> {
        if valid.contains(&ty) {
            return Ok(());
        }
        if !visiting.insert(ty) {
            return Err(Error {
                span,
                msg: "type can recursively refer to itself".to_string(),
            }
            .into());
        }

        match &self.types[ty].kind {
            TypeDefKind::List(Type::Id(id)) | TypeDefKind::Type(Type::Id(id)) => {
                self.validate_type_not_recursive(span, *id, visiting, valid)?
            }
            TypeDefKind::Variant(v) => {
                for case in v.cases.iter() {
                    if let Type::Id(id) = case.ty {
                        self.validate_type_not_recursive(span, id, visiting, valid)?;
                    }
                }
            }
            TypeDefKind::Record(r) => {
                for case in r.fields.iter() {
                    if let Type::Id(id) = case.ty {
                        self.validate_type_not_recursive(span, id, visiting, valid)?;
                    }
                }
            }
            TypeDefKind::Tuple(t) => {
                for ty in t.types.iter() {
                    if let Type::Id(id) = *ty {
                        self.validate_type_not_recursive(span, id, visiting, valid)?;
                    }
                }
            }

            TypeDefKind::Option(t) => {
                if let Type::Id(id) = *t {
                    self.validate_type_not_recursive(span, id, visiting, valid)?
                }
            }
            TypeDefKind::Expected(e) => {
                if let Type::Id(id) = e.ok {
                    self.validate_type_not_recursive(span, id, visiting, valid)?
                }
                if let Type::Id(id) = e.err {
                    self.validate_type_not_recursive(span, id, visiting, valid)?
                }
            }
            TypeDefKind::Stream(s) => {
                if let Type::Id(id) = s.element {
                    self.validate_type_not_recursive(span, id, visiting, valid)?
                }
                if let Type::Id(id) = s.end {
                    self.validate_type_not_recursive(span, id, visiting, valid)?
                }
            }
            TypeDefKind::Union(u) => {
                for c in u.cases.iter() {
                    if let Type::Id(id) = c.ty {
                        self.validate_type_not_recursive(span, id, visiting, valid)?
                    }
                }
            }

            TypeDefKind::Resource(_)
            | TypeDefKind::Flags(_)
            | TypeDefKind::List(_)
            | TypeDefKind::Type(_)
            | TypeDefKind::Enum(_) => {}
        }

        valid.insert(ty);
        visiting.remove(&ty);
        Ok(())
    }
}
