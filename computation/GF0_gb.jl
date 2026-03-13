#Gold = load("../computations/taylor_johnson29_graph.mrdi")
#=
es = [ Edge(2, 1), Edge(3, 2), Edge(4, 1), Edge(4, 3), Edge(5, 1), Edge(5, 4), Edge(6, 1), Edge(6, 2), Edge(7, 2), Edge(7, 3), Edge(8, 3), Edge(8, 4), Edge(10, 9), Edge(11, 10), Edge(12, 9), Edge(12, 11), Edge(13, 5), Edge(13, 6), Edge(13, 9), Edge(13, 10), Edge(14, 6), Edge(14, 7), Edge(14, 10), Edge(14, 11), Edge(15, 7), Edge(15, 8), Edge(15, 11), Edge(15, 12), Edge(16, 5), Edge(16, 8), Edge(16, 9), Edge(16, 12), Edge(18, 17), Edge(19, 18), Edge(20, 19), Edge(21, 20), Edge(22, 21), Edge(23, 22), Edge(24, 17), Edge(24, 23), Edge(25, 17), Edge(25, 18), Edge(26, 19), Edge(26, 20), Edge(26, 25), Edge(27, 23), Edge(27, 24), Edge(27, 25), Edge(28, 21), Edge(28, 22), Edge(28, 26), Edge(28, 27), Edge(29, 22), Edge(29, 23), Edge(30, 17), Edge(30, 24), Edge(30, 29), Edge(31, 20), Edge(31, 21), Edge(31, 29), Edge(32, 18), Edge(32, 19), Edge(32, 30), Edge(32, 31)];
G = Graph{Undirected}(32)
for e in es
  add_edge!(G, e.source, e.target)
end

q = quantum_automorphism_group(G)
groebner_basis(q);
save("taylor_johnson29_graph_qAut.mrdi", collect(q.gb))
=#

using Oscar
q_aut = load("/work/wack/taylor/Aut_GF.mrdi")
groebner_basis(q_aut)
save("/work/wack/taylor/GF_qAut_gb.mrdi", collect(q_aut.gb))

