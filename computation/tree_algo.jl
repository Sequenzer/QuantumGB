#Code to Run on the cluster
using QuantumGB

#n will be set by *.job file

n = 5
G1 = g1_named(n)
u = magic_unitary(n)
g = G1.gs
bg934 = bg(9,3,4,u=u)

x, y = recursive_reduction(bg934,g; bfs=true)

# Write the output to a file
filepath = "../data/conjecture_n_$(n).txt"

open(filepath, "w") do io
    println(io, str)
end


