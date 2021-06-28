------------------------------- MODULE typevars -------------------------------
\* a test that shows that parametric types can be instantiated
VARIABLE 
\* @type: Str -> Int;
strToInt,
\* @type: Int -> Str;
intToStr

\* Extend a function with a key -> value mapping
\* @type: (a -> b, a, b) => a -> b;
Extend(fun, key, value) == 
    [ k \in DOMAIN fun \union {key} |->
        IF k = key THEN value ELSE fun[k] ]

Init == 
  /\ strToInt = [ s \in {} |-> 0 ]
  /\ intToStr = [ i \in {} |-> "" ]

Next ==
  /\ strToInt' = Extend(strToInt, "a", 1)
  /\ intToStr' = Extend(intToStr, 1, "a")
    
===============================================================================
