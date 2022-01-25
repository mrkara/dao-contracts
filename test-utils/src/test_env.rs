use std::{
    path::PathBuf,
    sync::{Arc, Mutex},
};

use casper_engine_test_support::{
    DeployItemBuilder, ExecuteRequestBuilder, InMemoryWasmTestBuilder, ARG_AMOUNT,
    DEFAULT_ACCOUNT_INITIAL_BALANCE, DEFAULT_GENESIS_CONFIG, DEFAULT_GENESIS_CONFIG_HASH,
    DEFAULT_PAYMENT,
};
use casper_execution_engine::core::engine_state::{
    run_genesis_request::RunGenesisRequest, GenesisAccount,
};
use casper_types::{
    account::AccountHash, runtime_args, ContractPackageHash, Key, Motes, PublicKey, RuntimeArgs,
    SecretKey, U512, CLTyped, bytesrepr::{FromBytes, ToBytes}, URef,
};
use contract_utils::Address;

#[derive(Clone)]
pub struct TestEnv {
    state: Arc<Mutex<TestEnvState>>,
}

impl TestEnv {
    pub fn new() -> TestEnv {
        TestEnv {
            state: Arc::new(Mutex::new(TestEnvState::new())),
        }
    }

    pub fn deploy_wasm_file(&self, session_code: &str, session_args: RuntimeArgs) {
        self.state
            .lock()
            .unwrap()
            .deploy_wasm_file(session_code, session_args);
    }

    pub fn call_contract_package(
        &mut self,
        hash: ContractPackageHash,
        entry_point: &str,
        args: RuntimeArgs,
    ) {
        self.state
            .lock()
            .unwrap()
            .call_contract_package(hash, entry_point, args);
    }

    pub fn get_contract_package_hash(&self, name: &str) -> ContractPackageHash {
        self.state.lock().unwrap().get_contract_package_hash(name)
    }

    pub fn get_value<T: FromBytes + CLTyped>(&self, hash: ContractPackageHash, name: &str) -> T {
        self.state
            .lock()
            .unwrap()
            .get_value(hash, name)
    }

    pub fn get_dict_value<K: ToBytes + CLTyped, V: FromBytes + CLTyped + Default>(&self, hash: ContractPackageHash, name: &str, key: K) -> V {
        self.state
            .lock()
            .unwrap()
            .get_dict_value(hash, name, key)
    }

    pub fn active_account(&self) -> Address {
        self.state
            .lock()
            .unwrap()
            .active_account()
    }

    pub fn get_account(&self, n: usize) -> Address {
        self.state
            .lock()
            .unwrap()
            .get_account(n)
    }

    pub fn as_account(&self, account: Address) {
        self.state
            .lock()
            .unwrap()
            .as_account(account);
    }
}

impl Default for TestEnv {
    fn default() -> Self {
        TestEnv::new()
    }
}

pub struct TestEnvState {
    accounts: Vec<Address>,
    active_account: Address,
    context: InMemoryWasmTestBuilder,
}

impl TestEnvState {
    pub fn new() -> TestEnvState {
        let mut genesis_config = DEFAULT_GENESIS_CONFIG.clone();
        let mut accounts: Vec<Address> = Vec::new();
        for i in 0..3 {
            // Create keypair.
            let secret_key = SecretKey::ed25519_from_bytes([i; 32]).unwrap();
            let public_key = PublicKey::from(&secret_key);
    
            // Create an AccountHash from a public key.
            let account_addr = AccountHash::from(&public_key);
    
            // Create a GenesisAccount.
            let account = GenesisAccount::account(
                public_key,
                Motes::new(U512::from(DEFAULT_ACCOUNT_INITIAL_BALANCE)),
                None,
            );
            genesis_config.ee_config_mut().push_account(account);

            accounts.push(account_addr.into());
        }

        let run_genesis_request = RunGenesisRequest::new(
            *DEFAULT_GENESIS_CONFIG_HASH,
            genesis_config.protocol_version(),
            genesis_config.take_ee_config(),
        );

        let mut builder = InMemoryWasmTestBuilder::default();
        builder.run_genesis(&run_genesis_request).commit();

        TestEnvState {
            active_account: accounts[0],
            context: builder,
            accounts
        }
    }

    pub fn deploy_wasm_file(&mut self, wasm_path: &str, args: RuntimeArgs) {
        let session_code = PathBuf::from(wasm_path);

        let deploy_item = DeployItemBuilder::new()
            .with_empty_payment_bytes(runtime_args! {ARG_AMOUNT => *DEFAULT_PAYMENT})
            .with_authorization_keys(&[self.active_account_hash()])
            .with_address(self.active_account_hash())
            .with_session_code(session_code, args)
            .build();

        let execute_request = ExecuteRequestBuilder::from_deploy_item(deploy_item).build();
        self.context.exec(execute_request).commit().expect_success();
    }

    pub fn call_contract_package(
        &mut self,
        hash: ContractPackageHash,
        entry_point: &str,
        args: RuntimeArgs,
    ) {
        let deploy_item = DeployItemBuilder::new()
            .with_empty_payment_bytes(runtime_args! {ARG_AMOUNT => *DEFAULT_PAYMENT})
            .with_authorization_keys(&[self.active_account_hash()])
            .with_address(self.active_account_hash())
            .with_stored_versioned_contract_by_hash(hash.value(), None, entry_point, args)
            .build();

        let execute_request = ExecuteRequestBuilder::from_deploy_item(deploy_item).build();
        self.context.exec(execute_request).commit().expect_success();
    }

    pub fn get_contract_package_hash(&self, name: &str) -> ContractPackageHash {
        let account = self.context.get_account(self.active_account_hash()).unwrap();
        let key: &Key = account.named_keys().get(name).unwrap();
        ContractPackageHash::from(key.into_hash().unwrap())
    }

    pub fn get_value<T: FromBytes + CLTyped>(&self, hash: ContractPackageHash, name: &str) -> T {
        let contract_hash = self.context.get_contract_package(hash).unwrap().current_contract_hash().unwrap();

        // println!("{:#?}", self.context.get_contract(contract_hash));

        self.context.query(None, Key::Hash(contract_hash.value()), &[name.to_string()]).unwrap().as_cl_value().unwrap().clone().into_t().unwrap()
    }

    pub fn get_dict_value<K: ToBytes + CLTyped, V: FromBytes + CLTyped + Default>(&self, hash: ContractPackageHash, name: &str, key: K) -> V {
        let contract_hash = self.context.get_contract_package(hash).unwrap().current_contract_hash().unwrap();

        let dictionary_seed_uref: URef = self.context.get_contract(contract_hash).unwrap().named_keys().get(name).unwrap().as_uref().unwrap().clone();

        match self.context.query_dictionary_item(None, dictionary_seed_uref, &to_dictionary_key(&key)) {
            Ok(val) => {
                let value: V = val.as_cl_value().unwrap().clone().into_t::<V>().unwrap();
                value
            },
            Err(_) => V::default(),
        }
    }

    pub fn active_account(&self) -> Address {
        Address::from(self.active_account)
    }

    fn active_account_hash(&self) -> AccountHash {
        self.active_account().as_account_hash().unwrap().clone()
    }

    pub fn get_account(&self, n: usize) -> Address {
        self.accounts.get(n).unwrap().clone()
    }

    pub fn as_account(&mut self, account: Address) {
        self.active_account = account;
    }
}


fn to_dictionary_key<T: ToBytes>(key: &T) -> String {
    let preimage = key.to_bytes().unwrap();
    base64::encode(&preimage)
}