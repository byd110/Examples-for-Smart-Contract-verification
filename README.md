# Examples-for-Smart-Contract-verification
In the price oracle attack model. I abstract the function using data from price oracle in the example into two parts: 
1. Get data from price oracle.
2. Enter the condition statement to judge if the transaction are legit.
Based on this abstraction and the takeaway from the attack detection paper. I model the verification into three part:
1. In the precondition, I assume that we have failed on the first attempt to call the exploited function.
2. In the test method, I apply a instant arbitrary mutation to the data we got from price oracle.
3. In the postcondition, I check if the condition statement still holds.
