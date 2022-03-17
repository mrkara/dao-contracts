use casper_contract::contract_api::runtime;

use crate::{
    casper_env::{caller, emit},
    consts, Address, Error, Variable,
};

use self::events::OwnerChanged;

pub struct Owner {
    pub owner: Variable<Option<Address>>,
}

impl Default for Owner {
    fn default() -> Self {
        Self {
            owner: Variable::from(consts::NAME_OWNER),
        }
    }
}

impl Owner {
    pub fn init(&mut self, owner: Address) {
        self.change_ownership(owner);
    }

    pub fn change_ownership(&mut self, owner: Address) {
        self.owner.set(Some(owner));
        emit(OwnerChanged { new_owner: owner });
    }

    pub fn ensure_owner(&self) {
        if let Some(owner) = self.owner.get() {
            if owner != caller() {
                runtime::revert(Error::NotAnOwner) // User is not the owner.
            }
        } else {
            runtime::revert(Error::OwnerIsNotInitialized) // Owner is not inicialized.
        }
    }
}

pub mod events {
    use crate::Address;
    use casper_dao_macros::Event;

    #[derive(Debug, PartialEq, Event)]
    pub struct OwnerChanged {
        pub new_owner: Address,
    }
}
