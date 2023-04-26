
include "./NonNativeTypes.dfy"
include "./Contract.dfy"
include "./Token.dfy"

import opened NonNativeTypes

// datatype Msg = Msg(sender: Account, value: uint256)

// type Address = Account
datatype Proposal  = Proposal (sTime : uint160,  newOwner :Address)
datatype block = block (timestamp: uint160)

class Vote {
  var votingToken : map<Address,uint256>;
  var owner:Address;
  var proposal: Proposal;
  var block :block;
  ghost var totalamount : nat;

  method propose(msg:Msg)
    modifies this
    requires proposal.sTime == 0

  {
    proposal := Proposal(block.timestamp, msg.sender);
  }
  method vote(amount : uint256, msg:Msg)
    requires proposal.sTime as nat + 2  > block.timestamp as nat
    requires msg.sender !in votingToken ||  votingToken[msg.sender] as nat + amount as nat <= MAX_UINT256
    modifies this
  {
    mapAddVoting(votingToken, msg.sender, amount as nat);
    votingToken := votingToken[msg.sender :=(if msg.sender in votingToken then votingToken[msg.sender] else 0) + amount]; // transfer from sender to this contract using token's method.
    totalamount := totalamount + amount as nat;
  }

  method end(msg:Msg)
    modifies this
    requires proposal.sTime != 0
    requires proposal.sTime as nat + 2  < block.timestamp as nat
    ensures sum(votingToken) == totalamount
    //  requires sum(votingToken) == totalamount as nat
  {
    owner := proposal.newOwner;
  }
  constructor(msg: Msg)
  {
    votingToken := map[];
    owner := msg.sender;
    proposal := Proposal(0,msg.sender);
  }
}


lemma mapAddVoting(m: map<Address, uint256>, k: Address, v: nat)
  requires (if k in m then m[k] else 0) as nat + v <= MAX_UINT256
  ensures sum(m[k := ((if k in m then m[k] else 0) as nat + v) as uint256]) >= sum(m) + v

