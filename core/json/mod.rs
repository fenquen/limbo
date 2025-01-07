mod de;
mod error;
mod ser;

use std::rc::Rc;

pub use crate::json::de::from_str;
pub use crate::json::ser::to_string;
use crate::types::OwnedValue;
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
#[serde(untagged)]
pub enum Val {
    Null,
    Bool(bool),
    Integer(i64),
    Float(f64),
    String(String),
    Array(Vec<Val>),
    Object(IndexMap<String, Val>),
}

pub fn get_json(json_value: &OwnedValue) -> crate::Result<OwnedValue> {
    match json_value {
        OwnedValue::Text(ref t) => match from_str::<Val>(t) {
            Ok(json) => {
                let json = to_string(&json).unwrap();
                Ok(OwnedValue::Text(Rc::new(json)))
            }
            Err(_) => crate::bail_parse_error!("malformed JSON"),
        },
        OwnedValue::Blob(b) => {
            if let Ok(json) = jsonb::from_slice(b) {
                Ok(OwnedValue::Text(Rc::new(json.to_string())))
            } else {
                crate::bail_parse_error!("malformed JSON");
            }
        }
        _ => Ok(json_value.to_owned()),
    }
}
