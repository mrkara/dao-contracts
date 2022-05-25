use super::voting::VotingSummary;
use casper_dao_utils::casper_contract::contract_api::runtime;
use casper_dao_utils::Address;
use casper_types::runtime_args;
use casper_types::RuntimeArgs;

pub trait GovernanceVotingCallback {
    fn on_voting_finished(&self, summary: VotingSummary);
}

pub struct GovernanceVotingCallbackCaller {
    contract_package_hash: casper_types::ContractPackageHash,
}

impl GovernanceVotingCallback for GovernanceVotingCallbackCaller {
    fn on_voting_finished(&self, summary: VotingSummary) {
        runtime::call_versioned_contract(
            self.contract_package_hash,
            None,
            "on_voting_finished",
            runtime_args! {
                "summary" => summary
            },
        )
    }
}

impl GovernanceVotingCallbackCaller {
    pub fn at(contract_address: Address) -> Self {
        Self {
            contract_package_hash: *contract_address.as_contract_package_hash().unwrap(),
        }
    }
}
