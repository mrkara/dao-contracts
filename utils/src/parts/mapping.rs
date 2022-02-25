use std::{collections::BTreeMap, marker::PhantomData, sync::Mutex};

use casper_contract::{
    contract_api::{runtime, storage},
    unwrap_or_revert::UnwrapOrRevert,
};
use casper_types::{
    bytesrepr::{FromBytes, ToBytes},
    CLTyped, Key, URef,
};
use lazy_static::lazy_static;

use crate::casper_env::to_dictionary_key;

/// Data structure for storing key-value pairs.
/// 
/// It's is a wrapper on top of Casper's dictionary.
/// The main difference is that Mapping returns default value, if the value doesn't exists. 
pub struct Mapping<K, V> {
    name: String,
    key_ty: PhantomData<K>,
    value_ty: PhantomData<V>,
}

lazy_static! {
    static ref SEEDS: Mutex<BTreeMap<String, URef>> = Mutex::new(BTreeMap::new());
}

impl<K: ToBytes + CLTyped, V: ToBytes + FromBytes + CLTyped + Default> Mapping<K, V> {
    pub fn new(name: String) -> Self {
        Mapping {
            name,
            key_ty: PhantomData::<K>::default(),
            value_ty: PhantomData::<V>::default(),
        }
    }

    pub fn init(&self) {
        storage::new_dictionary(&self.name).unwrap_or_revert();
    }

    pub fn get(&self, key: &K) -> V {
        storage::dictionary_get(self.get_uref(), &to_dictionary_key(key))
            .unwrap_or_revert()
            .unwrap_or_default()
    }

    pub fn set(&self, key: &K, value: V) {
        storage::dictionary_put(self.get_uref(), &to_dictionary_key(key), value);
    }

    fn get_uref(&self) -> URef {
        let mut seeds = SEEDS.lock().unwrap();
        match seeds.get(&self.name) {
            Some(seed) => *seed,
            None => {
                let key: Key = runtime::get_key(&self.name).unwrap_or_revert();
                let seed: URef = *key.as_uref().unwrap_or_revert();
                seeds.insert(self.name.clone(), seed);
                seed
            }
        }
    }

    pub fn path(&self) -> &str {
        &self.name
    }
}

impl<K: ToBytes + CLTyped, V: ToBytes + FromBytes + CLTyped + Default> From<&str>
    for Mapping<K, V>
{
    fn from(name: &str) -> Self {
        Mapping::new(name.to_string())
    }
}
