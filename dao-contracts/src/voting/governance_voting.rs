//! Governance Voting module.
pub mod consts;
pub mod events;
pub mod voting;

use casper_dao_utils::casper_env::caller;
use casper_dao_utils::conversions::{u256_to_512, u512_to_u256};
use casper_dao_utils::{
    casper_contract::unwrap_or_revert::UnwrapOrRevert,
    casper_dao_macros::Instance,
    casper_env::{call_contract, emit, get_block_time, revert, self_address},
    Address, Error, Mapping, Variable,
};

use casper_types::{runtime_args, RuntimeArgs, U256, U512};


use self::voting::VotingSummary;
use self::{
    events::{BallotCast, VotingContractCreated, VotingCreated},
    voting::{Voting, VotingConfiguration},
};

use casper_dao_utils::VecMapping;

use super::ballot::Choice;
use super::VotingEnded;
use super::{ballot::VotingId, Ballot};

pub trait GovernanceVotingTrait {
    fn init(&mut self, reputation_token: Address);
}

/// Governance voting is a struct that contracts can use to implement voting. It consists of two phases:
/// 1. Informal voting
/// 2. Formal voting
///
/// Whether formal voting starts depends on informal voting results.
///
/// When formal voting passes, an action can be performed - a contract can be called with voted arguments.
///
/// Governance voting uses [Reputation Token](crate::ReputationContract) to handle reputation staking and
/// [Variable Repo](crate::VariableRepositoryContract) for reading voting configuration.
///
/// For example implementation see [AdminContract](crate::admin::AdminContract)
#[derive(Instance)]
pub struct GovernanceVoting {
    reputation_token: Variable<Address>,
    votings: Mapping<VotingId, Option<Voting>>,
    ballots: Mapping<(VotingId, Address), Ballot>,
    voters: VecMapping<VotingId, Address>,
    votings_count: Variable<U256>,
    dust_amount: Variable<U256>,
}

impl GovernanceVoting {
    /// Initializes the module with [Addresses](Address) of [Reputation Token](crate::ReputationContract) and [Variable Repo](crate::VariableRepositoryContract)
    ///
    /// # Events
    /// Emits [`VotingContractCreated`](VotingContractCreated)
    pub fn init(&mut self, variable_repo: Address, reputation_token: Address) {
        self.reputation_token.set(reputation_token);

        emit(VotingContractCreated {
            creator: caller(),
            reputation_token,
            voter_contract: self_address(),
        });
    }

    /// Creates new [Voting](Voting).
    ///
    /// # Events
    /// Emits [`VotingCreated`](VotingCreated)
    ///
    /// # Errors
    /// Throws [`Error::NotEnoughReputation`](casper_dao_utils::Error::NotEnoughReputation) when the creator does not have enough reputation to create a voting
    pub fn create_voting(
        &mut self,
        creator: Address,
        stake: U256,
        voting_configuration: VotingConfiguration,
    ) -> VotingId {
        if stake < voting_configuration.create_voting_minimum_reputation {
            revert(Error::NotEnoughReputation)
        }

        let voting_id = self.next_voting_id();
        let voting = Voting::new(voting_id, get_block_time(), voting_configuration);

        self.set_voting(voting);

        emit(VotingCreated {
            creator,
            voting_id,
            stake,
        });

        voting_id
    }

    /// Finishes voting.
    ///
    /// Depending on type of voting, different actions are performed.
    ///
    /// For informal voting a new formal voting can be created. Reputation staked for this voting is returned to the voters, except for creator. When voting
    /// passes, it is used as a stake for a new voting, otherwise it is burned.
    ///
    /// For formal voting an action will be performed if the result is in favor. Reputation is redistributed to the winning voters. When no quorum is reached,
    /// the reputation is returned, except for the creator - its reputation is then burned.
    ///
    /// # Events
    /// Emits [`VotingEnded`](VotingEnded), [`VotingCreated`](VotingCreated), [`BallotCast`](BallotCast)
    ///
    /// # Errors
    /// Throws [`FinishingCompletedVotingNotAllowed`](casper_dao_utils::Error::FinishingCompletedVotingNotAllowed) if trying to complete already finished voting
    ///
    /// Throws [`FormalVotingTimeNotReached`](casper_dao_utils::Error::FormalVotingTimeNotReached) if formal voting time did not pass
    ///
    /// Throws [`InformalVotingTimeNotReached`](casper_dao_utils::Error::InformalVotingTimeNotReached) if informal voting time did not pass
    ///
    /// Throws [`ArithmeticOverflow`](casper_dao_utils::Error::ArithmeticOverflow) in an unlikely event of a overflow when calculating reputation to redistribute
    pub fn finish_voting(&mut self, voting_id: VotingId) -> VotingSummary {
        let voting = self
            .get_voting(voting_id)
            .unwrap_or_revert_with(Error::VotingDoesNotExist);

        if voting.completed() {
            revert(Error::FinishingCompletedVotingNotAllowed)
        }

        if !voting.is_in_time(get_block_time()) {
            revert(Error::VotingTimeNotReached)
        }

        let voters_len = self.voters.len(voting.voting_id());
        let voting_result = voting.get_result(voters_len);
        
        if voting.voting_configuration().redistribute_reputation {
            self.redistribute_reputation(&voting);
        }

        voting.complete();

        emit(VotingEnded {
            voting_id: voting.voting_id(),
            result: voting_result.to_string(),
            votes_count: voters_len.into(),
            stake_in_favor: voting.stake_in_favor(),
            stake_against: voting.stake_against(),
        });

        self.set_voting(voting);

        let voting_summary = VotingSummary::new(
            voting_result,
            voting_id,
        );

        self.callback(&voting, voting_summary);

        voting_summary
    }

    fn callback(&self, voting: &Voting, voting_summary: VotingSummary) {
        let callback_address = voting.voting_configuration().callback_address;
        let callback_entrypoint = voting.voting_configuration().callback_entrypoint;

        if callback_address.is_some() && callback_entrypoint.is_some() {
            call_contract(
                callback_address.unwrap_or_revert(),
                callback_entrypoint.unwrap_or_revert().as_str(),
                runtime_args! {
                    "voting_summary" => voting_summary
                },
            )
        }
    }

    /// Casts a vote
    ///
    /// # Events
    /// Emits [`BallotCast`](BallotCast)
    ///
    /// # Errors
    /// Throws [`VoteOnCompletedVotingNotAllowed`](casper_dao_utils::Error::VoteOnCompletedVotingNotAllowed) if voting is completed
    ///
    /// Throws [`CannotVoteTwice`](casper_dao_utils::Error::CannotVoteTwice) if voter already voted
    pub fn vote(&mut self, voter: Address, voting_id: U256, choice: Choice, stake: U256) {
        let mut voting = self.get_voting(voting_id).unwrap_or_revert();

        // We cannot vote on a completed voting
        if voting.completed() {
            revert(Error::VoteOnCompletedVotingNotAllowed)
        }

        let mut vote = self.ballots.get(&(voting_id, voter)).unwrap_or_default();
        match vote.voter {
            Some(_) => {
                // Cannot vote twice on the same voting
                revert(Error::CannotVoteTwice)
            }
            None => {
                // Stake the reputation
                self.transfer_reputation(voter, self_address(), stake);

                // Create a new vote
                vote = Ballot {
                    voter: Some(voter),
                    choice,
                    voting_id,
                    stake,
                };
                // Add a voter to the list
                self.voters.add(voting_id, voter);
            }
        }

        // Update the votes list
        self.ballots.set(&(voting_id, voter), vote);

        // update voting
        voting.stake(stake, choice);
        self.set_voting(voting);

        emit(BallotCast {
            voter,
            voting_id,
            choice,
            stake,
        });
    }

    /// Returns the dust amount.
    ///
    /// Those are leftovers from redistribution of reputation tokens. For example, when 10 tokens needs to be redistributed between 3 voters,
    /// each will recieve 3 reputation, with 1 reputation left in the contract's balance.
    pub fn get_dust_amount(&self) -> U256 {
        self.dust_amount.get().unwrap_or_default()
    }
    /// Returns the address of [Reputation Token](crate::ReputationContract) connected to the contract
    pub fn get_reputation_token_address(&self) -> Address {
        self.reputation_token.get().unwrap_or_revert()
    }

    /// Returns the [Ballot](Ballot) of voter with `address` and cast on `voting_id`
    pub fn get_ballot(&self, voting_id: U256, address: Address) -> Option<Ballot> {
        self.ballots.get_or_none(&(voting_id, address))
    }

    /// Returns the nth [Ballot](Ballot) of cast on `voting_id`
    pub fn get_ballot_at(&mut self, voting_id: U256, i: u32) -> Ballot {
        let address = self
            .get_voter(voting_id, i)
            .unwrap_or_revert_with(Error::VoterDoesNotExist);
        self.get_ballot(voting_id, address)
            .unwrap_or_revert_with(Error::BallotDoesNotExist)
    }

    /// Returns the address of nth voter who voted on Voting with `voting_id`
    pub fn get_voter(&self, voting_id: VotingId, at: u32) -> Option<Address> {
        self.voters.get_or_none(voting_id, at)
    }

    /// Returns the [Voting](Voting) for given id
    pub fn get_voting(&self, voting_id: VotingId) -> Option<Voting> {
        self.votings
            .get_or_none(&voting_id)
            .map(|x| x.unwrap_or_revert())
    }

    fn set_voting(&self, voting: Voting) {
        self.votings.set(&voting.voting_id(), Some(voting))
    }

    fn next_voting_id(&mut self) -> U256 {
        let voting_id = self.votings_count.get().unwrap_or_default();
        self.votings_count.set(voting_id + 1);
        voting_id
    }

    fn transfer_reputation(&mut self, owner: Address, recipient: Address, amount: U256) {
        if amount == U256::zero() {
            return;
        }

        let args: RuntimeArgs = runtime_args! {
            "owner" => owner,
            "recipient" => recipient,
            "amount" => amount,
        };

        call_contract(self.get_reputation_token_address(), "transfer_from", args)
    }

    fn burn_reputation(&mut self, owner: Address, amount: U256) {
        let args: RuntimeArgs = runtime_args! {
            "owner" => owner,
            "amount" => amount,
        };

        call_contract(self.get_reputation_token_address(), "burn", args)
    }

    fn burn_creators_and_return_others_reputation(&mut self, voting_id: VotingId) {
        for i in 0..self.voters.len(voting_id) {
            let ballot = self.get_ballot_at(voting_id, i);
            if i == 0 {
                // the creator
                self.burn_reputation(self_address(), ballot.stake);
            } else {
                // the voters - transfer from contract to them
                self.transfer_reputation(
                    self_address(),
                    ballot.voter.unwrap_or_revert(),
                    ballot.stake,
                );
            }
        }
    }

    fn return_reputation(&mut self, voting_id: VotingId) {
        for i in 0..self.voters.len(voting_id) {
            let ballot = self.get_ballot_at(voting_id, i);
            self.transfer_reputation(
                self_address(),
                ballot.voter.unwrap_or_revert(),
                ballot.stake,
            );
        }
    }

    fn redistribute_reputation(&mut self, voting: &Voting) {
        // TODO: redistribute depending on configuration
        // TODO: update conversion after support for U256<>U512 conversion will be added to Casper
        let total_stake = u256_to_512(voting.total_stake()).unwrap_or_revert();
        let mut transferred = U512::zero();
        let result = voting.is_in_favor();
        let u256_max = u256_to_512(U256::MAX).unwrap_or_revert();

        for i in 0..self.voters.len(voting.voting_id()) {
            let ballot = self.get_ballot_at(voting.voting_id(), i);
            if ballot.choice.is_in_favor() == result {
                let to_transfer = total_stake * u256_to_512(ballot.stake).unwrap_or_revert()
                    / u256_to_512(voting.get_winning_stake()).unwrap_or_revert();

                if to_transfer > u256_max {
                    revert(Error::ArithmeticOverflow)
                }

                transferred += to_transfer;

                let to_transfer =
                    u512_to_u256(to_transfer).unwrap_or_revert_with(Error::ArithmeticOverflow);

                self.transfer_reputation(
                    self_address(),
                    ballot.voter.unwrap_or_revert(),
                    to_transfer,
                );
            }
        }

        // mark leftovers
        let dust = total_stake - transferred;

        if dust > U512::zero() {
            if dust > u256_max {
                revert(Error::ArithmeticOverflow)
            }

            self.dust_amount.set(
                self.get_dust_amount()
                    + u512_to_u256(dust).unwrap_or_revert_with(Error::ArithmeticOverflow),
            );
        }
    }
}
