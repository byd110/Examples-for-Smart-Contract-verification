
//The model for the price oracle contract that has bug

class LendingContract  {

  var collateral : nat;
  var token1 : nat;
  var token2 : nat;

  ghost var inv : nat;



  predicate valid()
    reads this
  {
    token1 * token2 == inv && token2 != 0 && token1 != 0

  }

  // applicaiotn contract function using price oracle data
  function method customized_price () : nat
    requires valid()
    reads this

  {
    token1 / token2
  }

  // update data from price oracle
  method update (tok1 : nat, tok2 : nat)
    requires valid()
    requires tok1 * tok2 == inv
    requires tok2 != 0

    modifies this

    ensures valid()
    ensures inv == old(inv)
    ensures token1 == tok1 && token2 == tok2
    ensures collateral == old(collateral)
  {
    token1 := tok1;
    token2 := tok2;
  }

  method mutate ()
    requires valid()
    requires inv >= 4

    modifies this

    ensures valid()
    ensures inv == old(inv)
    // ensures token1 != old(token1) && token2 != old(token2)
    ensures collateral == old(collateral)
  {
    var m : nat := mut();
    var data1m := token1 * m;
    var data2m := token2 / m;
    update(data1m, data2m);
  }

  /*we assume that the first attempt to use feedback data from price oracle has failed, and see if the second attempt will succeed after mutate the data.*/
  method test(amount : nat) returns ( price : nat)
    requires valid()
    requires amount > 0
    requires collateral != 0
    requires amount  > token1 / token2 * collateral //this precondition means the former attempt to use feedback data from price oracle has failed
    requires inv >= 4

    modifies this

    ensures  price * collateral < amount

  {
    mutate();
    price := customized_price();
  }

  method  mut() returns (a: nat)
    ensures a > 0 && a != 1
    ensures token2 % a == 0


}

method {:extern} havoc() returns (a: nat)
  ensures a != 0



