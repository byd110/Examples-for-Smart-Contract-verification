

include "./NonNativeTypes.dfy"
include "./Contract.dfy"
include "./Token.dfy"

import opened NonNativeTypes


class Lottery {
  // user address -> lottery id -> count
  var tickets : map<Address , map<uint128 , uint>>;
  var winningId : uint128; // the winning id
  var drawingPhase : bool ; // whether the owner is drawing
  ghost var totalbought : nat;


  method enterDrawingPhase()
    modifies this
  {
    drawingPhase := true;
    var k : Address := *;
    // if k in tickets{
    //   totalbought := totalbought + sums(tickets[k]);
    // }
  }
  // id is randomly chosen off-chain, i.e., by chainlink

  method draw(id : uint128)
    requires winningId == 0
    requires drawingPhase
    requires id != 0
    modifies this
  {
    winningId := id;
  }


  method multiBuy(ids: seq<uint128>, amounts : seq<uint>, msg:Msg)

    requires winningId == 0
    requires |amounts| == |ids|
    modifies this
    ensures drawingPhase == false
  {
    var totalAmount : uint := 0;
    var i := 0;
    // assert(); // make sure it's buying phase.
    while i < |ids| {
      var index : uint128 := ids[i];
      var amount : uint := amounts[i];
      assume(msg.sender in tickets);
      var m : map<uint128 , uint> := tickets[msg.sender];
      assume((if index in tickets[msg.sender] then tickets[msg.sender][index] else 0) as nat + amount as nat < MAX_UINT256);
      m := m[index := (if index in tickets[msg.sender] then tickets[msg.sender][index] else 0) + amount];
      tickets := tickets[msg.sender := m];
      // tickets[msg.sender] := tickets[msg.sender][index := tickets[msg.sender][index] + amount];
      // tickets := tickets[msg.sender := tickets[msg.sender][ids[i] := tickets[msg.sender][ids[i]] + amounts[i]]];
      assume(totalAmount as nat + amount as nat < MAX_UINT256);
      totalAmount := totalAmount + amount;
      i := i + 1;
    }
  }

  constructor(msg: Msg)
  {
    tickets := map[];
    winningId := 0;
    drawingPhase := false;
    totalbought := 0;
  }
}

function sums(m: map<uint128 , nat>): nat
  ensures sums(map[]) == 0