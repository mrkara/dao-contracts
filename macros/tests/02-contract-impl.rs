use casper_dao_macros::{casper_contract_interface, CasperContract};

#[derive(Default, CasperContract)]
struct ImportantContract {}

#[casper_contract_interface]
trait ImportantContractInterface {
    fn init(&mut self);
    fn mint(&mut self, recipient: casper_dao_utils::Address, amount: casper_types::U256);
    fn burn(&mut self, owner: casper_dao_utils::Address, amount: casper_types::U256);
}

fn main() {
    ImportantContract::install();
    ImportantContract::entry_points();
}
