Coq has 4 "big" types:

Prop is meant for propositions. It is impredicative, meaning that you can instantiate polymorphic functions with polymorphic types. It is also erased at run-time, meaning you can't pattern match on a Prop value to build a Type value, unless there's only one possibility.

SProp is like Prop, but with definitional proof irrelevance, meaning that if p1,p2:P
 then p1=p2

Set is meant for computation. It's predicative, and doesn't have proof irrelevance, which lets you do nice things like not assuming 1=2. The Set parts remain during code extraction.

Type is a supertype of both of these, allowing you to write code once that works with either