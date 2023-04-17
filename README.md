# Examples-for-Smart-Contract-verification
In the price oracle attack model. I abstract the function using data from price oracle in the example into two parts: 
  1. Get data from price oracle.
  2. Enter the condition statement to judge if the transaction are legit.

Based on this abstraction and the takeaway from the attack detection paper. I model the verification into three part:
  1. In the precondition, I assume that we have failed on the first attempt to call the exploited function.
  2. In the test method, I apply a instant arbitrary mutation to the data we got from price oracle.
  3. In the postcondition, I check if the condition statement still holds.

A small problem: I try to write a time varying GetPrice algorithm in Valid edition. But the problem is that Dafny report a error in mutate() about the post condition 'ensures token1 != old(token1) && token2 != old(token2)' that ensures that I do mutate the price. The verification costs a lot of time to run. And if you check the counter example Dafny gives for this error, it is like we have price a and b for token1 and token2, and a mutation factor m>1. Then after the code mutate the price of token1 by token1 := a * m, and the result price in counter example is still a. In short, it returns a * m == a where m>1. I am still not able to find the reason for this.  
