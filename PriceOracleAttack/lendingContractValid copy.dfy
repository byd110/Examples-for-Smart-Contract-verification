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



class LendingContract  {

  var collateral : nat;
  var token1 : nat;
  var token2 : nat;
  var lastinquire : nat;
  var timestamp : nat;
  var lastprice : nat;
  ghost var inv : nat;
  const MAX_UINT256 : nat := (0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 as nat - 1)


  predicate valid()
    reads this
  {
    token1 * token2 >= inv && token2 != 0 && token1 != 0 && inv != 0

  }

  // applicaiotn contract function using price oracle data
  function method customized_price () : nat
    requires valid()
    requires timestamp >= lastinquire
    reads this

  {
    if timestamp <= lastinquire + 1 then lastprice else token1 / token2
  }

  // update data from price oracle
  method update (tok1 : nat, tok2 : nat)
    requires valid()
    requires tok1 * tok2 >= inv
    requires tok2 != 0

    modifies this

    ensures valid()
    ensures inv >= old(inv)
    ensures token1 == tok1 && token2 == tok2
    ensures timestamp == old(timestamp) && lastinquire == old(lastinquire)
    ensures lastprice == old(lastprice)
    ensures collateral == old(collateral)
  {
    token1 := tok1;
    token2 := tok2;
    inv := tok1 * tok2;
  }

  method mutate ()
    requires valid()
    requires inv >= 4
    ensures timestamp == old(timestamp) && lastinquire == old(lastinquire)

    modifies this

    ensures valid()
    ensures inv >= old(inv)
    // ensures token1 != old(token1) && token2 != old(token2)
    ensures timestamp == old(timestamp) && lastinquire == old(lastinquire)
    ensures lastprice == old(lastprice)
    ensures collateral == old(collateral)
  {
    var m : nat := mut();
    var data1m := token1 * m;
    var data2m := token2 / m;
    update(data1m, data2m);
    // assume(token1 != old(token1) && token2 != old(token2));
  }

  /*we assume that the first attempt to use feedback data from price oracle has failed, and see if the second attempt will succeed after mutate the data.*/
  method test(amount : nat) returns ( price : nat)
    requires valid()
    requires amount > 0
    requires collateral != 0
    requires amount  > token1 / token2 * collateral  /*this precondition means the former attempt to use feedback data from price oracle has failed*/
    requires inv >= 4
    requires lastinquire == timestamp  /*this indicate that the mutate of data is transient change.*/
    // requires lastprice == token1 / token2

    modifies this

    ensures  price * collateral < amount  /*the statement to determine whether attempt is seccess or not*/

  {
    lastprice := token1 / token2;
    mutate();
    price := customized_price();
  }

  method  mut() returns (a: nat)
    ensures a > 0 && a != 1
    ensures token2 % a == 0


}

method {:extern} havoc() returns (a: nat)
  ensures a != 0



