use casper_types::ApiError;

/// All possible errors that can be raised by the utils crate.
#[derive(Debug, PartialEq)]
pub enum Error {
    NotAnOwner,
    OwnerIsNotInitialized,
    NotWhitelisted,
    InsufficientBalance,
    InsufficientAllowance,
    TotalSupplyOverflow,
    ValueNotAvailable,
    ActivationTimeInPast,
    Unknown,
    NoSuchMethod(String),
    InvalidContext,
    TokenDoesNotExist,
    TokenAlreadyExists,
    ApprovalToCurrentOwner,
    ApproveCallerIsNotOwnerNorApprovedForAll,
    TransferCallerIsNotOwnerNorApproved,
    TransferToNonERC721ReceiverImplementer,
    TransferFromIncorrectOwner,
    TransferToNone,
    ApproveToCaller,
}

impl From<Error> for ApiError {
    fn from(val: Error) -> Self {
        let id = match val {
            Error::InsufficientBalance => 404,
            Error::InsufficientAllowance => 401,
            Error::NotAnOwner => 1000,
            Error::OwnerIsNotInitialized => 1001,
            Error::NotWhitelisted => 1002,
            Error::TotalSupplyOverflow => 1004,
            Error::ValueNotAvailable => 1005,
            Error::ActivationTimeInPast => 1006,
            Error::InvalidContext => 1099,
            Error::Unknown => 1100,
            Error::NoSuchMethod(_) => 1101,
            Error::TokenDoesNotExist => 1700,
            Error::TokenAlreadyExists => 1701,
            Error::ApprovalToCurrentOwner => 1702,
            Error::ApproveCallerIsNotOwnerNorApprovedForAll => 1703,
            Error::TransferCallerIsNotOwnerNorApproved => 1704,
            Error::TransferToNonERC721ReceiverImplementer => 1705,
            Error::TransferFromIncorrectOwner => 1706,
            Error::TransferToNone => 1707,
            Error::ApproveToCaller => 1708,
        };
        ApiError::User(id)
    }
}

impl From<u16> for Error {
    fn from(val: u16) -> Self {
        match val {
            401 => Error::InsufficientAllowance,
            404 => Error::InsufficientBalance,
            1000 => Error::NotAnOwner,
            1001 => Error::OwnerIsNotInitialized,
            1002 => Error::NotWhitelisted,
            1004 => Error::TotalSupplyOverflow,
            1005 => Error::ValueNotAvailable,
            1006 => Error::ActivationTimeInPast,
            1700 => Error::TokenDoesNotExist,
            1701 => Error::TokenAlreadyExists,
            1702 => Error::ApprovalToCurrentOwner,
            1703 => Error::ApproveCallerIsNotOwnerNorApprovedForAll,
            1704 => Error::TransferCallerIsNotOwnerNorApproved,
            1705 => Error::TransferToNonERC721ReceiverImplementer,
            1706 => Error::TransferFromIncorrectOwner,
            1707 => Error::TransferToNone,
            1708 => Error::ApproveToCaller,
            _ => Error::Unknown,
        }
    }
}
