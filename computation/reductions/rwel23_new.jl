#test
s1 = Iterators.product([2,3,:g], [2], [2,3,:g], [3,:g]);
s1 = Iterators.filter(x -> x[3] == :g || x[1] == :g || x[3] != x[1], s1);
s1tagged = TaggedTuple[x[3] == :g && x[1] == :g ? (x, Symbol[:g31]) : (x,Symbol[]) for x in s1];



