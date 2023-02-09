#![cfg_attr(
    not(feature = "contracts"),
    feature(proc_macro_hygiene, stmt_expr_attributes)
)]

pub mod gcd;
pub mod union_find;
