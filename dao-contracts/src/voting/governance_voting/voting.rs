//! Voting struct with logic for governance voting
use crate::voting::ballot::{Choice, VotingId};
use casper_dao_utils::{
    casper_dao_macros::{CLTyped, FromBytes, ToBytes},
    Address,
};
use casper_types::U256;

use super::consts;

/// Result of a Voting
#[derive(PartialEq, Clone, CLTyped, FromBytes, ToBytes)]
pub enum VotingResult {
    InFavor,
    Against,
    QuorumNotReached,
}

impl ToString for VotingResult {
    fn to_string(&self) -> String {
        match self {
            VotingResult::InFavor => consts::VOTING_PASSED.to_string(),
            VotingResult::Against => consts::VOTING_REJECTED.to_string(),
            VotingResult::QuorumNotReached => consts::VOTING_QUORUM_NOT_REACHED.to_string(),
        }
    }
}

/// Type of Voting (Formal or Informal)
#[derive(Debug, PartialEq, CLTyped, FromBytes, ToBytes)]
pub enum VotingType {
    Informal,
    Formal,
}

/// Finished Voting summary
#[allow(dead_code)]
#[derive(CLTyped, FromBytes, ToBytes)]
pub struct VotingSummary {
    result: VotingResult,
    voting_id: VotingId,
}

impl VotingSummary {
    pub fn new(result: VotingResult, voting_id: VotingId) -> Self {
        Self { result, voting_id }
    }

    fn is_rejected(&self) -> bool {
        vec![VotingResult::Against, VotingResult::QuorumNotReached].contains(&self.result)
    }

    pub fn result(&self) -> VotingResult {
        self.result.clone()
    }

    /// Get the voting summary's voting id.
    pub fn voting_id(&self) -> U256 {
        self.voting_id
    }
}

/// Voting configuration, created and persisted since voting start
#[derive(Debug, Default, Clone, CLTyped, ToBytes, FromBytes, PartialEq)]
pub struct VotingConfiguration {
    pub voting_quorum: U256,
    pub voting_time: u64,
    pub create_voting_minimum_reputation: U256,
    pub vote_minimum_reputation: U256,
    pub redistribute_reputation: bool,
    pub mint_reputation: U256,
    pub callback_address: Option<Address>,
}

/// Voting struct
#[derive(Debug, CLTyped, ToBytes, FromBytes, PartialEq)]
pub struct Voting {
    voting_id: VotingId,
    completed: bool,
    stake_in_favor: U256,
    stake_against: U256,
    start_time: u64,
    voting_configuration: VotingConfiguration,
}

impl Voting {
    /// Creates new Voting with immutable VotingConfiguration
    pub fn new(
        voting_id: U256,
        start_time: u64,
        voting_configuration: VotingConfiguration,
    ) -> Self {
        Voting {
            voting_id,
            completed: false,
            stake_in_favor: U256::zero(),
            stake_against: U256::zero(),
            start_time,
            voting_configuration,
        }
    }

    pub fn can_be_completed(&self, block_time: u64) -> bool {
        !self.completed && !self.is_in_time(block_time)
    }

    /// Sets voting as completed
    pub fn complete(&mut self) {
        self.completed = true;
    }

    /// Returns if voting is still in voting phase
    pub fn is_in_time(&self, block_time: u64) -> bool {
        self.start_time + self.voting_configuration.voting_time <= block_time
    }

    pub fn is_in_favor(&self) -> bool {
        self.stake_in_favor >= self.stake_against
    }

    /// Depending on the result of the voting, returns the amount of reputation staked on the winning side
    pub fn get_winning_stake(&self) -> U256 {
        match self.is_in_favor() {
            true => self.stake_in_favor,
            false => self.stake_against,
        }
    }

    pub fn get_quorum(&self) -> U256 {
        self.voting_configuration.voting_quorum
    }

    pub fn get_result(&self, voters_number: u32) -> VotingResult {
        if self.get_quorum().as_u32() > voters_number {
            VotingResult::QuorumNotReached
        } else if self.is_in_favor() {
            VotingResult::InFavor
        } else {
            VotingResult::Against
        }
    }

    pub fn stake(&mut self, stake: U256, choice: Choice) {
        // overflow is not possible due to reputation token having U256 as max
        match choice {
            Choice::InFavor => self.stake_in_favor += stake,
            Choice::Against => self.stake_against += stake,
        }
    }

    pub fn total_stake(&self) -> U256 {
        // overflow is not possible due to reputation token having U256 as max
        self.stake_in_favor + self.stake_against
    }

    /// Get the voting's voting id.
    pub fn voting_id(&self) -> U256 {
        self.voting_id
    }

    /// Get the voting's completed.
    pub fn completed(&self) -> bool {
        self.completed
    }

    /// Get the voting's stake in favor.
    pub fn stake_in_favor(&self) -> U256 {
        self.stake_in_favor
    }

    /// Get the voting's stake against.
    pub fn stake_against(&self) -> U256 {
        self.stake_against
    }

    /// Get the voting's formal voting quorum.
    pub fn voting_quorum(&self) -> U256 {
        self.voting_configuration.voting_quorum
    }

    /// Get the voting's formal voting time.
    pub fn voting_time(&self) -> u64 {
        self.voting_configuration.voting_time
    }

    /// Get a reference to the voting's voting configuration.
    #[must_use]
    pub fn voting_configuration(&self) -> &VotingConfiguration {
        &self.voting_configuration
    }
}

#[test]
fn test_voting_serialization() {
    use casper_types::bytesrepr::FromBytes;
    use casper_types::bytesrepr::ToBytes;

    let voting = Voting {
        voting_id: VotingId::from(1),
        completed: false,
        stake_in_favor: U256::zero(),
        stake_against: U256::zero(),
        start_time: 123,
        voting_configuration: VotingConfiguration {
            voting_quorum: U256::from(1),
            voting_time: 100,
            create_voting_minimum_reputation: U256::from(10),
            vote_minimum_reputation: U256::from(0),
            redistribute_reputation: true,
            mint_reputation: U256::from(1000),
            callback_address: None,
        },
    };

    let (voting2, _bytes) = Voting::from_bytes(&voting.to_bytes().unwrap()).unwrap();

    assert_eq!(voting.voting_id(), voting2.voting_id());
    assert_eq!(
        voting.voting_configuration.voting_quorum,
        voting2.voting_configuration.voting_quorum
    );
    assert_eq!(voting.stake_against, voting2.stake_against);
    assert_eq!(voting.stake_in_favor, voting2.stake_in_favor);
    assert_eq!(voting.completed, voting2.completed);
    assert_eq!(
        voting.voting_configuration.voting_time,
        voting2.voting_configuration.voting_time
    );
    assert_eq!(voting.start_time, voting2.start_time);
}
