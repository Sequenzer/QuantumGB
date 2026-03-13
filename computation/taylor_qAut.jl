using Oscar

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
qgb = load("/work/wack/taylor/taylor_johnson29_graph_qAut.mrdi")
R = parent(qgb[1])

u = Matrix{Generic.FreeAssociativeAlgebraElem{QQFieldElem}}(undef, 32, 32);
for i in 1:32
  for j in 1:32
    u[i,j] = R[(i-1)*32+j]
  end
end
u = transpose(u)

x = ideal_membership(u[4,17], qgb;algorithm=:f4)
save("contains_u417.mrdi", x)

#=
is_in = ideal_membership(f,qgb;algorithm=:f4)
save("contains_commutator_u44_u17u17.mrdi", is_in)

using Oscar
q1 = load("/work/wack/taylor/taylor_qaut.mrdi");

R = parent(q1[1])
u = Matrix{Generic.FreeAssociativeAlgebraElem{QQFieldElem}}(undef, 16, 16);
for i in 1:16
  for j in 1:16
    u[i,j] = R[(i-1)*16+j]
  end
end
u = collect(transpose(u))

q1ans = Dict{Tuple{Int,Int,Int,Int}, Int}()
for (i,j) in Iterators.product(1:16, 1:16)
  for (k,h) in Iterators.product(1:16, 1:16)
    if i == k || j == h 
      q1ans[(i,j,k,h)] = 0
      continue
    end
    if (k>=i) || (k==i && h>=j)
      q1ans[(i,j,k,h)] = 0
      continue
    end
    mon = u[i,j]*u[k,h]
    if ideal_membership(mon, q1;algorithm=:f4)
      q1ans[(i,j,k,h)] = 1
      println("Monomial relation in qA1: ", mon)
      continue
    end

    f = u[i,j]*u[k,h] - u[k,h]*u[i,j]
    if iszero(f)
      q1ans[(i,j,k,h)] = 2
      println("Zero commutator relation in qA1: ", f)
      continue
    end

    if !ideal_membership(f, q1;algorithm=:f4)
      q1ans[(i,j,k,h)] = -1
      println("WARN!!! Found a non-included commutator relation in qA1: ", f)
    else
      q1ans[(i,j,k,h)] = 3
      println("Commutator relation in qA1: ", f)
    end
  end
end
save("taylor_qaut_commutators.mrdi", q1ans)

q2 = load("johnson29_qaut.mrdi");

R = parent(q2[1])
u = Matrix{Generic.FreeAssociativeAlgebraElem{QQFieldElem}}(undef, 16, 16);
for i in 1:16
  for j in 1:16
    u[i,j] = R[(i-1)*16+j]
  end
end
u = collect(transpose(u))

q2ans = Dict{Tuple{Int,Int,Int,Int}, Int}()
for (i,j) in Iterators.product(1:16, 1:16)
  for (k,h) in Iterators.product(1:16, 1:16)
    if i == k || j == h 
      q2ans[(i,j,k,h)] = 0
      continue
    end
    if (k>=i) || (k==i && h>=j)
      q2ans[(i,j,k,h)] = 0
      continue
    end
    mon = u[i,j]*u[k,h]
    if ideal_membership(mon, q2;algorithm=:f4)
      q2ans[(i,j,k,h)] = 1
      println("Monomial relation in qA1: ", mon)
      continue
    end

    f = u[i,j]*u[k,h] - u[k,h]*u[i,j]
    if iszero(f)
      q2ans[(i,j,k,h)] = 2
      println("Zero commutator relation in qA1: ", f)
      continue
    end

    if !ideal_membership(f, q2;algorithm=:f4)
      q2ans[(i,j,k,h)] = -1
      println("WARN!!! Found a non-included commutator relation in qA1: ", f)
    else
      q2ans[(i,j,k,h)] = 3
      println("Commutator relation in qA1: ", f)
    end
  end
end
save("johnson29_qaut_commutators.mrdi", q2ans)

using Oscar
L = load("/work/wack/taylor/taylor.poly")
G1 = vertex_edge_graph(L)
G2 = vertex_edge_graph(johnson_solid(29))
A1 = Int.(collect(adjacency_matrix(G1)))
A2 = Int.(collect(adjacency_matrix(G2)))
A1 = QQ.(A1)
A2 = QQ.(A2)
A1 = matrix(ZZ,adjacency_matrix(G1))
A2 = matrix(ZZ,adjacency_matrix(G2))
eigenvalues(A1)
eigenvalues(A2)
eigenspaces(A1)
p1 = characteristic_polynomial(A1)
x = gens(parent(p1))[1]
p1 = p1//((x-4)*(x-0)^3*(x+2)^2)
K = splitting_field(p1.num)
eigenvalues_with_multiplicities(K,A1)

p2 = characteristic_polynomial(A2)
x = gens(parent(p2))[1]
p2 = p2//((x-2)*(x-4)*(x-0)*(x+2))
K2 = splitting_field(p2.num)
eigenvalues_with_multiplicities(K2,A2)

roots(p1)


roots(p2)
K = algebraic_closure(QQ)
eigenvalues_with_multiplicities(K,A2)
=#
