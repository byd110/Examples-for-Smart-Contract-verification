/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

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

  // invoked every day to reset a round
  //  function reset()  onlyOwner {
  //  delete tickets;
  //  winningId = 0; drawingPhase = false;
  //  }
  //  function buy(uint64 id, uint amount)  {
  //  require(winningId == 0, "already drawn");
  //  require(!drawingPhase, "drawing")
  //  receivePayment(msg.sender, amount),
  //  tickets[msg.sender][id] += amount;
  //  }

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
    modifies this
    ensures drawingPhase == false
  {
    var totalAmount : uint := 0;
    var i := 0;
    assume(|amounts| >= |ids|);
    // assert(); // make sure it's buying phase.
    while i < |ids| {
      var index : uint128 := ids[i];
      var amount : uint := amounts[i];
      assume(msg.sender in tickets);
      var m : map<uint128 , uint> := tickets[msg.sender];
      assume((if index in tickets[msg.sender] then tickets[msg.sender][index] else 0) as nat + amount as nat < MAX_UINT256);
      m := m[index := (if index in tickets[msg.sender] then tickets[msg.sender][index] else 0) + amount];
      tickets := tickets[msg.sender := m];
      //   tickets[msg.sender] := tickets[msg.sender][index := tickets[msg.sender][index] + amount];
      //   tickets := tickets[msg.sender := tickets[msg.sender][ids[i] := tickets[msg.sender][ids[i]] + amounts[i]]];
      assume(totalAmount as nat + amount as nat < MAX_UINT256);
      totalAmount := totalAmount + amount;
      i := i + 1;
    }
  }
  //  receivePayment(msg.sender, totalAmount),
  //  }
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