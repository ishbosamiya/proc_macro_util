//! Proc macro utilities that can be used with all proc macro crates.

use std::marker::PhantomData;

use itertools::Itertools;
use proc_macro2::TokenStream;

/// Trait to compare between different attributes. See
/// [`AttributeOr`], [`AttributeAnd`], [`AttributeNot`].
pub trait AttributeComparison<A> {
    /// Test if the given attributes `A` satisfy `self`.
    fn test(&self, attributes: &[A]) -> bool;

    /// Display the comparison test as a string.
    fn display(&self) -> String;
}

/// And operation on two attributes.
pub struct AttributeAnd<T, U> {
    one: T,
    two: U,
}

impl<T, U> AttributeAnd<T, U> {
    /// Create a new [`AttributeAnd`].
    #[allow(dead_code)]
    pub const fn new(one: T, two: U) -> Self {
        Self { one, two }
    }
}

impl<A, T: AttributeComparison<A>, U: AttributeComparison<A>> AttributeComparison<A>
    for AttributeAnd<T, U>
{
    fn test(&self, attributes: &[A]) -> bool {
        self.one.test(attributes) && self.two.test(attributes)
    }

    fn display(&self) -> String {
        format!("({} && {})", self.one.display(), self.two.display())
    }
}

/// Or operation on two attributes.
pub struct AttributeOr<T, U> {
    one: T,
    two: U,
}

impl<T, U> AttributeOr<T, U> {
    /// Create a new [`AttributeOr`].
    pub const fn new(one: T, two: U) -> Self {
        Self { one, two }
    }
}

impl<A, T: AttributeComparison<A>, U: AttributeComparison<A>> AttributeComparison<A>
    for AttributeOr<T, U>
{
    fn test(&self, attributes: &[A]) -> bool {
        self.one.test(attributes) || self.two.test(attributes)
    }

    fn display(&self) -> String {
        format!("({} || {})", self.one.display(), self.two.display())
    }
}

/// Not the attribute `T`.
pub struct AttributeNot<T> {
    val: T,
}

impl<T> AttributeNot<T> {
    /// Create a new [`AttributeNot`].
    #[allow(dead_code)]
    pub const fn new(val: T) -> Self {
        Self { val }
    }
}

impl<A, T: AttributeComparison<A>> AttributeComparison<A> for AttributeNot<T> {
    fn test(&self, attributes: &[A]) -> bool {
        !self.val.test(attributes)
    }

    fn display(&self) -> String {
        format!("!{}", self.val.display())
    }
}

impl<T: PartialEq + AttributeIdentifier> AttributeComparison<T> for T {
    fn test(&self, attributes: &[T]) -> bool {
        attributes.contains(self)
    }

    fn display(&self) -> String {
        let joined = self.identifier().join("|");
        if self.identifier().len() > 1 {
            format!("({})", joined)
        } else {
            joined
        }
    }
}

pub trait AttributeIdentifier {
    /// Get the attribute identifier for `self`.
    ///
    /// This would be the list of attributes that become [`Self`]
    /// after parsing.
    fn identifier(&self) -> &'static [&'static str];

    /// Does the given [`struct@syn::Ident`] match any of the
    /// identifiers of [`Self`].
    fn identifier_matches(&self, ident: &syn::Ident) -> bool {
        self.identifier().iter().any(|i| ident == i)
    }
}

/// Container attribute requirement.
pub trait ContainerAttributeRequirement {
    /// Container attribute data.
    type ContainerAttributeData: ContainerAttributeDataRequirement;

    /// Get a reference to the [`TokenStream`] of the entire container
    /// attribute.
    fn get_token_stream(&self) -> &TokenStream;

    /// Get a reference to the [`Self::ContainerAttributeData`].
    fn get_attribute_data(&self) -> &Self::ContainerAttributeData;
}

/// Container attribute data requirement.
pub trait ContainerAttributeDataRequirement {
    /// Container attribute type.
    type ContainerAttributeType: ContainerAttributeTypeRequirement;

    /// Get the corresponding [`Self::ContainerAttributeType`].
    fn to_type(&self) -> Self::ContainerAttributeType;
}

/// Container attribute type requirement.
pub trait ContainerAttributeTypeRequirement:
    AttributeIdentifier + PartialEq + Eq + std::hash::Hash + Sized + 'static
{
    /// Type for [`Self::REQUIRED_ATTRIBUTES`].
    type RequiredAttributes: AttributeComparison<Self>;

    /// Required attributes for the container.
    const REQUIRED_ATTRIBUTES: Option<Self::RequiredAttributes>;

    /// Corresponding [`FieldAttributeTypeRequirement`].
    type FieldAttributeType: FieldAttributeTypeRequirement;

    /// Get all the possible [`Self`]s.
    fn all() -> &'static [Self];

    /// Is only a single usage of this container attribute allowed in the
    /// container?
    ///
    /// If true, the attribute can be used only once for the
    /// container. If false, the attribute can be used multiple times
    /// for the container.
    fn is_unique_per_container(&self) -> bool;

    /// Get list of container attributes `self` is incompatible with.
    ///
    /// It is important to have the incompatibility specified both
    /// ways. It can be thought of as requiring a directed graph where
    /// each edge of the graph must have an edge that is exactly
    /// opposite to it. This constraint is checked for at run time.
    fn incompatible_with(&self) -> &'static [Self];

    /// Get list of field attributes `self` is incompatible with.
    ///
    /// It is important to have this incompatibility specified both
    /// ways. It can be thought of as requiring a directed graph where
    /// each edge of the graph must have an edge that is exactly
    /// opposite to it. This contraint is checked at run time.
    fn incompatible_with_field_attrs(&self) -> &'static [Self::FieldAttributeType] {
        &[]
    }
}

/// Empty container attribute type.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EmptyContainerAttributeType<FieldAttributeType> {
    _field_attr_type: PhantomData<FieldAttributeType>,
}

impl<FieldAttributeType: FieldAttributeTypeRequirement>
    EmptyContainerAttributeType<FieldAttributeType>
{
    /// Create a new [`EmptyContainerAttributeType`].
    pub fn new() -> Self {
        Self {
            _field_attr_type: PhantomData,
        }
    }
}

impl<FieldAttributeType: FieldAttributeTypeRequirement> Default
    for EmptyContainerAttributeType<FieldAttributeType>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<FieldAttributeType: FieldAttributeTypeRequirement> ContainerAttributeTypeRequirement
    for EmptyContainerAttributeType<FieldAttributeType>
{
    type RequiredAttributes = Self;

    const REQUIRED_ATTRIBUTES: Option<Self::RequiredAttributes> = None;

    type FieldAttributeType = FieldAttributeType;

    fn all() -> &'static [Self] {
        todo!()
    }

    fn is_unique_per_container(&self) -> bool {
        todo!()
    }

    fn incompatible_with(&self) -> &'static [Self] {
        todo!()
    }
}

impl<FieldAttribute: FieldAttributeTypeRequirement> AttributeIdentifier
    for EmptyContainerAttributeType<FieldAttribute>
{
    fn identifier(&self) -> &'static [&'static str] {
        &[]
    }
}

/// Empty field attribute type.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct EmptyFieldAttributeType<ContainerAttributeType> {
    _container_attr_type: PhantomData<ContainerAttributeType>,
}

impl<ContainerAttributeType: ContainerAttributeTypeRequirement>
    EmptyFieldAttributeType<ContainerAttributeType>
{
    /// Create a new [`EmptyFieldAttributeType`].
    pub fn new() -> Self {
        Self {
            _container_attr_type: PhantomData,
        }
    }
}

impl<ContainerAttributeType: ContainerAttributeTypeRequirement> Default
    for EmptyFieldAttributeType<ContainerAttributeType>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<ContainerAttributeType: ContainerAttributeTypeRequirement> FieldAttributeTypeRequirement
    for EmptyFieldAttributeType<ContainerAttributeType>
{
    type RequiredAttributesSingleFieldType = Self;

    const REQUIRED_ATTRIBUTES_SINGLE_FIELD: Option<Self::RequiredAttributesSingleFieldType> = None;

    type ContainerAttributeType = ContainerAttributeType;

    fn all() -> &'static [Self] {
        &[]
    }

    fn is_unique_per_field(&self) -> bool {
        true
    }

    fn is_unique_per_struct(&self) -> bool {
        false
    }

    fn incompatible_with_same_field(&self) -> &'static [Self] {
        &[]
    }
}

impl<ContainerAttribute: ContainerAttributeTypeRequirement> AttributeIdentifier
    for EmptyFieldAttributeType<ContainerAttribute>
{
    fn identifier(&self) -> &'static [&'static str] {
        &[]
    }
}

/// Verify attribute compatibility.
///
/// `container_attributes`: List of
/// [`ContainerAttributeRequirement`]s.
pub fn verify_container_attributes_compatibility<
    ContainerAttribute: ContainerAttributeRequirement,
>(
    container_attributes: &[ContainerAttribute],
) -> Result<(), syn::Error> {
    let container_attribute_types = container_attributes
        .iter()
        .map(|attr| attr.get_attribute_data().to_type())
        .collect::<Vec<_>>();

    if let Some(required_attributes) = <<ContainerAttribute::ContainerAttributeData
                                         as ContainerAttributeDataRequirement>::ContainerAttributeType
                                        as ContainerAttributeTypeRequirement>::REQUIRED_ATTRIBUTES {
        if !required_attributes.test(&container_attribute_types) {
            return Err(syn::Error::new_spanned(
                container_attributes
                    .iter()
                    .map(|attr| attr.get_token_stream())
                    .fold(TokenStream::new(), |mut acc, token_stream| {
                        acc.extend(std::iter::once(token_stream.clone()));
                        acc
                    }),
                format!("attributes requirement {} not satisfied", required_attributes.display()),
            ));
        }
    }

    container_attributes
        .iter()
        .filter(|attr| {
            attr.get_attribute_data()
                .to_type()
                .is_unique_per_container()
        })
        .duplicates_by(|attr| attr.get_attribute_data().to_type())
        .try_for_each(|attr| {
            Err(syn::Error::new_spanned(
                attr.get_token_stream(),
                "multiple definitions of the attribute is not supported",
            ))
        })?;

    // verify the incompatibility graph is built correctly. Each edge
    // must have a corresponding edge that is in the exact opposite
    // direction
    let all_container_attribute_types = <<ContainerAttribute::ContainerAttributeData
                                         as ContainerAttributeDataRequirement>::ContainerAttributeType
                                        as ContainerAttributeTypeRequirement>::all();
    all_container_attribute_types.iter().for_each(|attr| {
        attr.incompatible_with()
            .iter()
            .for_each(|incompatible_attr| {
                assert!(incompatible_attr.incompatible_with().contains(attr));
            });
    });

    // ensure no incompatible attributes are defined at once
    container_attributes
        .iter()
        .zip_eq(container_attribute_types.iter())
        .try_for_each(|(attr, attr_type)| {
            attr_type
                .incompatible_with()
                .iter()
                .try_for_each(|incompatible_attr_type| {
                    if container_attribute_types.contains(incompatible_attr_type) {
                        let incompatible_attr = container_attributes
                            .iter()
                            .find(|attr| {
                                attr.get_attribute_data().to_type() == *incompatible_attr_type
                            })
                            .unwrap();
                        Err(syn::Error::new_spanned(
                            {
                                let mut ts = attr.get_token_stream().clone();
                                ts.extend(std::iter::once(
                                    incompatible_attr.get_token_stream().clone(),
                                ));
                                ts
                            },
                            format!(
                                "incompatible attributes `{}` `{}`",
                                attr_type.display(),
                                incompatible_attr_type.display()
                            ),
                        ))
                    } else {
                        Ok(())
                    }
                })
        })?;

    Ok(())
}

/// Field attribute requirement.
pub trait FieldAttributeRequirement {
    /// Field attribute data.
    type FieldAttributeData: FieldAttributeDataRequirement;

    /// Get a reference to the [`TokenStream`] of the entire field
    /// attribute.
    fn get_token_stream(&self) -> &TokenStream;

    /// Get a reference to the [`Self::FieldAttributeData`].
    fn get_attribute_data(&self) -> &Self::FieldAttributeData;
}

/// Field attribute data requirement.
pub trait FieldAttributeDataRequirement {
    /// Field attribute type.
    type FieldAttributeType: FieldAttributeTypeRequirement;

    /// Get the corresponding [`Self::FieldAttributeType`].
    fn to_type(&self) -> Self::FieldAttributeType;
}

/// Field attribute type requirement.
pub trait FieldAttributeTypeRequirement:
    AttributeIdentifier + PartialEq + Eq + std::hash::Hash + Sized + 'static
{
    /// Type for [`Self::REQUIRED_ATTRIBUTES_SINGLE_FIELD`].
    type RequiredAttributesSingleFieldType: AttributeComparison<Self>;

    /// Required attributes for a single field. This means that each
    /// field is expected to have these attributes defined.
    const REQUIRED_ATTRIBUTES_SINGLE_FIELD: Option<Self::RequiredAttributesSingleFieldType>;

    /// Corresponding [`ContainerAttributeTypeRequirement`].
    type ContainerAttributeType: ContainerAttributeTypeRequirement;

    /// Get all the possible [`Self`]s.
    fn all() -> &'static [Self];

    /// Is only a single usage of this field attribute allowed for the
    /// field?
    ///
    /// If true, the attribute can be used only once per field. If
    /// false, the attribute can be defined multiple times on the same
    /// field.
    fn is_unique_per_field(&self) -> bool;

    /// Is only a single usage of this field attribute allowed in the
    /// struct?
    ///
    /// If true, the attribute can be used only once in the struct
    /// (thus only one field of the struct can have this
    /// attribute). If false, multiple fields can have this attribute
    /// defined.
    fn is_unique_per_struct(&self) -> bool;

    /// Get list of field attributes `self` is incompatible with when
    /// defined within the same field.
    ///
    /// It is important to have the incompatibility specified both
    /// ways. It can be thought of as requiring a directed graph where
    /// each edge of the graph must have an edge that is exactly
    /// opposite to it. This constraint is checked for at run time.
    fn incompatible_with_same_field(&self) -> &'static [Self];

    /// Get list of container attributes `self` is incompatible with.
    ///
    /// It is important to have this incompatibility specified both
    /// ways. It can be thought of as requiring a directed graph where
    /// each edge of the graph must have an edge that is exactly
    /// opposite to it. This contraint is checked at run time.
    fn incompatible_with_container_attrs(&self) -> &'static [Self::ContainerAttributeType] {
        &[]
    }
}

/// Verify attribute compatibility.
///
/// `field_attributes`: List of [`FieldAttributeRequirement`]s for
/// each field of the struct.
pub fn verify_field_attributes_compatibility<FieldAttribute: FieldAttributeRequirement>(
    fields_attributes: &[Vec<FieldAttribute>],
) -> Result<(), syn::Error> {
    let fields_attribute_types = fields_attributes
        .iter()
        .map(|attrs| {
            attrs
                .iter()
                .map(|attr| attr.get_attribute_data().to_type())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    if let Some(required_attributes) = <<FieldAttribute::FieldAttributeData
                                         as FieldAttributeDataRequirement>::FieldAttributeType
                                        as FieldAttributeTypeRequirement>::REQUIRED_ATTRIBUTES_SINGLE_FIELD {
        fields_attributes
            .iter()
            .zip_eq(fields_attribute_types.iter())
            .try_for_each(|(field_attributes, field_attribute_types)| {
                if required_attributes.test(field_attribute_types) {
                    Ok(())
                } else {
                    Err(syn::Error::new_spanned(
                        field_attributes.iter().map(|attr| attr.get_token_stream()).fold(
                            TokenStream::new(),
                            |mut acc, token_stream| {
                                acc.extend(std::iter::once(token_stream.clone()));
                                acc
                            },
                        ),
                        format!("attributes requirement {} not satisfied", required_attributes.display()),
                    ))
                }
            })?;
    }

    fields_attributes
        .iter()
        .map(|attrs| {
            attrs
                .iter()
                .filter(|attr| attr.get_attribute_data().to_type().is_unique_per_field())
                .duplicates_by(|attr| attr.get_attribute_data().to_type())
                .try_for_each(|attr| {
                    Err(syn::Error::new_spanned(
                        attr.get_token_stream(),
                        "multiple definitions of attribute on same field not supported",
                    ))
                })
        })
        .collect::<Result<Vec<()>, _>>()?;

    fields_attributes
        .iter()
        .flat_map(|attrs| {
            attrs
                .iter()
                .filter(|attr| attr.get_attribute_data().to_type().is_unique_per_struct())
                .unique_by(|attr| attr.get_attribute_data().to_type())
        })
        .duplicates_by(|attr| attr.get_attribute_data().to_type())
        .try_for_each(|attr| {
            Err(syn::Error::new_spanned(
                attr.get_token_stream(),
                "attribute must be used only on one field of the field",
            ))
        })?;

    // verify the incompatibility graph is built correctly. Each edge
    // must have a corresponding edge that is in the exact opposite
    // direction
    let all_field_attribute_types = <<FieldAttribute::FieldAttributeData
                                      as FieldAttributeDataRequirement>::FieldAttributeType
                                     as FieldAttributeTypeRequirement>::all();
    all_field_attribute_types.iter().for_each(|attr| {
        attr.incompatible_with_same_field()
            .iter()
            .for_each(|incompatible_attr| {
                assert!(incompatible_attr
                    .incompatible_with_same_field()
                    .contains(attr));
            });
    });

    // ensure no incompatible attributes are defined at once for the
    // same field
    fields_attributes
        .iter()
        .zip_eq(fields_attribute_types.iter())
        .map(|(attrs, attr_types)| {
            attrs
                .iter()
                .zip_eq(attr_types.iter())
                .try_for_each(|(attr, attr_type)| {
                    attr_type
                        .incompatible_with_same_field()
                        .iter()
                        .try_for_each(|incompatible_attr_type| {
                            if attr_types.contains(incompatible_attr_type) {
                                let incompatible_attr = attrs
                                    .iter()
                                    .find(|attr| {
                                        attr.get_attribute_data().to_type()
                                            == *incompatible_attr_type
                                    })
                                    .unwrap();
                                Err(syn::Error::new_spanned(
                                    {
                                        let mut ts = attr.get_token_stream().clone();
                                        ts.extend(std::iter::once(
                                            incompatible_attr.get_token_stream().clone(),
                                        ));
                                        ts
                                    },
                                    format!(
                                        "incompatible attributes `{}` `{}`",
                                        attr_type.display(),
                                        incompatible_attr_type.display()
                                    ),
                                ))
                            } else {
                                Ok(())
                            }
                        })
                })
        })
        .collect::<Result<Vec<()>, _>>()?;

    Ok(())
}

/// Verify compatibility between container and field attributes.
///
/// `container_attributes`: List of [`ContainerAttributeRequirement`]s
/// of the struct.
///
/// `field_attributes`: List of [`FieldAttributeRequirement`]s for
/// each field of the struct.
pub fn verify_container_and_field_attributes_compatibility<
    ContainerAttribute,
    ContainerAttributeData,
    ContainerAttributeType,
    FieldAttribute,
    FieldAttributeData,
    FieldAttributeType,
>(
    container_attributes: &[ContainerAttribute],
    fields_attributes: &[Vec<FieldAttribute>],
) -> Result<(), syn::Error>
where
    ContainerAttribute:
        ContainerAttributeRequirement<ContainerAttributeData = ContainerAttributeData>,
    ContainerAttributeData:
        ContainerAttributeDataRequirement<ContainerAttributeType = ContainerAttributeType>,
    ContainerAttributeType:
        ContainerAttributeTypeRequirement<FieldAttributeType = FieldAttributeType>,
    FieldAttribute: FieldAttributeRequirement<FieldAttributeData = FieldAttributeData>,
    FieldAttributeData: FieldAttributeDataRequirement<FieldAttributeType = FieldAttributeType>,
    FieldAttributeType:
        FieldAttributeTypeRequirement<ContainerAttributeType = ContainerAttributeType>,
{
    // verify the incompatibility graph is built correctly. Each edge
    // must have a corresponding edge that is in the exact opposite
    // direction
    {
        let all_container_attribute_types = <<ContainerAttribute::ContainerAttributeData
                                              as ContainerAttributeDataRequirement>::ContainerAttributeType
                                             as ContainerAttributeTypeRequirement>::all();
        all_container_attribute_types
            .iter()
            .for_each(|container_attr_type| {
                container_attr_type
                    .incompatible_with_field_attrs()
                    .iter()
                    .for_each(|incompatible_field_attr_type| {
                        assert!(incompatible_field_attr_type
                            .incompatible_with_container_attrs()
                            .iter()
                            .any(|incompatible_container_attr_type| {
                                incompatible_container_attr_type == container_attr_type
                            }));
                    });
            });

        let all_field_attribute_types = <<FieldAttribute::FieldAttributeData
                                          as FieldAttributeDataRequirement>::FieldAttributeType
                                         as FieldAttributeTypeRequirement>::all();

        all_field_attribute_types
            .iter()
            .for_each(|field_attr_type| {
                field_attr_type
                    .incompatible_with_container_attrs()
                    .iter()
                    .for_each(|incompatible_container_attr_type| {
                        assert!(incompatible_container_attr_type
                            .incompatible_with_field_attrs()
                            .iter()
                            .any(|incompatible_field_attr_type| {
                                incompatible_field_attr_type == field_attr_type
                            }));
                    });
            });
    }

    // ensure no incompatible attributes are defined between the
    // container attributes and the field attributes
    //
    // since the graph is already verified to have an edge in both
    // directions, it is possible to test from the field attributes to
    // the container attributes.
    fields_attributes.iter().try_for_each(|field_attributes| {
        field_attributes.iter().try_for_each(|field_attr| {
            let field_attr_type = field_attr.get_attribute_data().to_type();

            field_attr_type
                .incompatible_with_container_attrs()
                .iter()
                .try_for_each(|incompatible_container_attr_type| {
                    match container_attributes.iter().find(|container_attr| {
                        *incompatible_container_attr_type
                            == container_attr.get_attribute_data().to_type()
                    }) {
                        Some(incompatible_container_attr) => Err(syn::Error::new_spanned(
                            {
                                let mut ts = field_attr.get_token_stream().clone();
                                ts.extend(std::iter::once(
                                    incompatible_container_attr.get_token_stream().clone(),
                                ));
                                ts
                            },
                            format!(
                                "incompatible attributes `{}` `{}`",
                                field_attr_type.display(),
                                incompatible_container_attr_type.display()
                            ),
                        )),
                        None => Ok(()),
                    }
                })
        })
    })?;

    Ok(())
}

/// Parse the given [`struct@syn::LitStr`] as a function.
///
/// This is just an alias for [`parse_lit_str_into_expr_path()`] to
/// make the intent clearer.
pub fn parse_lit_str_as_function(s: &syn::LitStr) -> syn::parse::Result<syn::ExprPath> {
    parse_lit_str_into_expr_path(s)
}

/// Parse the given [`struct@syn::LitStr`] into [`struct@syn::Ident`].
pub fn parse_lit_str_into_ident(s: &syn::LitStr) -> syn::parse::Result<syn::Ident> {
    parse_lit_str(s)
}

/// Parse the given [`struct@syn::LitStr`] into [`enum@syn::Type`].
pub fn parse_lit_str_into_type(s: &syn::LitStr) -> syn::parse::Result<syn::Type> {
    parse_lit_str(s)
}

/// Parse the given [`struct@syn::LitStr`] into [`enum@syn::Expr`].
pub fn parse_lit_str_into_expr(s: &syn::LitStr) -> syn::parse::Result<syn::Expr> {
    parse_lit_str(s)
}

/// Parse the given [`struct@syn::LitStr`] into [`enum@syn::Visibility`].
pub fn parse_lit_str_into_visibility(s: &syn::LitStr) -> syn::parse::Result<syn::Visibility> {
    parse_lit_str(s)
}

/// Parse the given [`struct@syn::LitStr`] into [`struct@syn::ExprPath`].
///
/// reference: serde-rs - serde_derive/src/internals/attr.rs
pub fn parse_lit_str_into_expr_path(s: &syn::LitStr) -> syn::parse::Result<syn::ExprPath> {
    parse_lit_str(s)
}

/// Parse the given [`struct@syn::LitStr`] into a generic `T` that can parse
/// token streams.
///
/// reference: serde-rs - serde_derive/src/internals/attr.rs
fn parse_lit_str<T>(s: &syn::LitStr) -> syn::parse::Result<T>
where
    T: syn::parse::Parse,
{
    let tokens = spanned_tokens(s)?;
    syn::parse2(tokens)
}

/// Convert the given [`struct@syn::LitStr`] into a [`TokenStream`] with the
/// span of the [`struct@syn::LitStr`].
///
/// reference: serde-rs - serde_derive/src/internals/attr.rs
fn spanned_tokens(s: &syn::LitStr) -> syn::parse::Result<TokenStream> {
    let stream = syn::parse_str(&s.value())?;
    Ok(respan(stream, s.span()))
}

/// Respan the given [`TokenStream`] with the given
/// [`proc_macro2::Span`].
///
/// reference: serde-rs - serde_derive/src/internals/attr.rs
fn respan(stream: TokenStream, span: proc_macro2::Span) -> TokenStream {
    stream
        .into_iter()
        .map(|token| respan_token(token, span))
        .collect()
}

/// Respan the [`proc_macro2::TokenTree`] provided with the [`provided
/// proc_macro2::Span`].
///
/// reference: serde-rs - serde_derive/src/internals/attr.rs
fn respan_token(
    mut token: proc_macro2::TokenTree,
    span: proc_macro2::Span,
) -> proc_macro2::TokenTree {
    if let proc_macro2::TokenTree::Group(g) = &mut token {
        *g = proc_macro2::Group::new(g.delimiter(), respan(g.stream(), span));
    }
    token.set_span(span);
    token
}

#[cfg(test)]
mod test {
    use crate::{
        AttributeAnd, AttributeComparison, AttributeIdentifier, AttributeNot, AttributeOr,
    };

    #[derive(PartialEq, Eq, Hash)]
    enum Attr {
        A,
        B,
        C,
    }

    impl AttributeIdentifier for Attr {
        fn identifier(&self) -> &'static [&'static str] {
            match self {
                Attr::A => &["a"],
                Attr::B => &["b"],
                Attr::C => &["c"],
            }
        }
    }

    #[test]
    fn attribute_comparison_test_01() {
        let required_attrs = AttributeAnd::new(
            Attr::A,
            AttributeOr::new(AttributeNot::new(Attr::B), Attr::C),
        );

        assert!(required_attrs.test(&[Attr::A]));
        assert!(required_attrs.test(&[Attr::A, Attr::C]));
        assert!(!required_attrs.test(&[Attr::A, Attr::B]));
        assert!(!required_attrs.test(&[Attr::C]));
    }

    #[test]
    fn attribute_comparison_test_02() {
        let required_attrs = AttributeOr::new(
            AttributeAnd::new(Attr::A, Attr::B),
            AttributeAnd::new(AttributeNot::new(Attr::A), AttributeNot::new(Attr::B)),
        );

        assert!(required_attrs.test(&[]));
        assert!(required_attrs.test(&[Attr::A, Attr::B]));
        assert!(required_attrs.test(&[Attr::C]));
        assert!(!required_attrs.test(&[Attr::A]));
        assert!(!required_attrs.test(&[Attr::B]));
        assert!(!required_attrs.test(&[Attr::A, Attr::C]));
        assert!(!required_attrs.test(&[Attr::B, Attr::C]));
    }

    #[test]
    fn attribute_comparison_display_01() {
        let required_attrs = AttributeAnd::new(
            Attr::A,
            AttributeOr::new(AttributeNot::new(Attr::B), Attr::C),
        );

        assert_eq!(required_attrs.display(), "(a && (!b || c))");
    }
}
