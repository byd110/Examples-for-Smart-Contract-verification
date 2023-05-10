// see the whole process as whole, set specs to every step and the whole method and see the specs has conflict or not.
class lottery{
  var tickets : map<nat, map<nat, nat>>;
  var winningId : nat;
  var drawingPhase : bool;
  var allnumbers : seq<nat>;
  var mempoolBuffer : bool;
  var owner : nat;


  method main()
    modifies this
  {
    // 1. start lottery (could have a buying attempt during starting and started lottery)
    startLottery();

    // 2. buy tickets
    var id, numbers, amounts := select();
    multiBuy(id, numbers, amounts);
    // buyTicket(id, numbers[0], amounts[0]);

    // 3. start drawing (end buying tickets)
    mempoolBuffer := true;

    // 4. buying attempt
    id, numbers, amounts := select();
    multiBuy(id, numbers, amounts);
    // buyTicket(id, numbers[0], amounts[0]);

    // 5. drawing started (end buying scuessfully)
    drawingPhase := true;
    mempoolBuffer := false;

    // 6. buying attempt
    id, numbers, amounts := select();
    multiBuy(id, numbers, amounts);
    // buyTicket(id, numbers[0], amounts[0]);

    // 7. draw
    var winner := havoc();
    mempoolBuffer := true;

    // 8. buying attempt
    numbers := [winner];
    amounts := [amounts[0]];
    multiBuy(id, numbers, amounts);
    // buyTicket(id, winner, amounts[0]);

    // 9. end drawing
    draw(winner);
    mempoolBuffer := false;

    // 10. buying attempt
    numbers := [winner];
    amounts := [amounts[0]];
    multiBuy(id, numbers, amounts);
    // buyTicket(id, winner, amounts[0]);
  }

  method startLottery()
    modifies this
    ensures drawingPhase == false
    ensures winningId == 0
    ensures forall id : nat, ticketnum : nat:: id in tickets && ticketnum in tickets[id] ==> tickets[id][ticketnum] == 0
  {
    drawingPhase := false;
    winningId := 0;
    tickets := map[];
    mempoolBuffer := false;
  }

  method select() returns (id :nat, numbers : seq<nat>, amounts : seq<nat>)
    ensures |numbers| == |amounts| && |numbers| > 0
    ensures forall i : nat :: i < |amounts| ==> amounts[i] > 0
    ensures forall j : nat :: j in numbers ==> j in allnumbers


  method buyTicket(id : nat, number: nat, amount : nat)
    requires amount > 0
    requires drawingPhase == false
    requires winningId == 0
    requires number in allnumbers
    modifies this
    ensures drawingPhase == false
    ensures winningId == 0
    ensures number in allnumbers
    // ensures tickets[id][number] >= old(tickets[id][number]) + amount
  {
    // tickets := tickets[id:= tickets[id][number:= tickets[id][number] + amount]];
  }

  method multiBuy(id : nat, numbers : seq<nat>, amounts : seq<nat>)
    requires |numbers| == |amounts| && |numbers| > 0
    requires forall i : nat :: i < |amounts| ==> amounts[i] > 0
    requires forall j : nat :: j in numbers ==> j in allnumbers
    requires winningId == 0



  method draw(id : nat)
    requires winningId == 0
    requires drawingPhase
    requires id != 0
    modifies this
  {
    winningId := id;
  }

  method havoc() returns (r : nat)
    ensures r > 0
    ensures r in allnumbers

}


