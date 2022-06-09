include "BaseTypes.dfy"
  
module ErrorCodes
{
  import opened BaseTypes
  // TODO: make numeric values the same as in the Rust node
  const InsufficientFunds:uint := 400;
  const ContractAlreadyDeployed:uint := 401;
  const UnknownFunctionId:uint := 402;
  const IncorrectMessage:uint := 403;
  const ComputePhaseFailed:uint := 404;
  const ComputePhaseSkipped:uint := 405;
  const ActionPhaseFailed:uint := 406;
  const BouncePhaseFailed:uint := 407;
  const MessageBounced:uint := 408;
  const InternalMessageExpected:uint := 409;
}
