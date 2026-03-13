using Oscar


function compute_minor(M::Matrix, i::Int, j::Int)
    rows = [k for k in 1:size(M,1) if k != i]
    cols = [l for l in 1:size(M,2) if l != j]
    return M[rows, cols]
end


function det_2(S::Matrix)
    return S[1,1]*S[2,2] - S[1,2]*S[2,1]
end


function left(S::Matrix)
  return reshape([(-1)^(i+j) * det_2(compute_minor(S,i,j)) for i in 1:3, j in 1:3], 3, 3)
end


function get_equations(S::Matrix, T::Matrix)
    EQ1 = determinant(T)
    L = left(S)
    Left_side = L * T
    EQ2 = Left_side[1,1]
    EQ3 = Left_side[2,2]
    EQ4 = Left_side[3,3]
    return ideal([EQ1, EQ2, EQ3, EQ4])
end

using Oscar

function determinant(S::Matrix)
    return S[1,1]*S[2,2]*S[3,3] +
           S[1,2]*S[2,3]*S[3,1] +
           S[1,3]*S[2,1]*S[3,2] -
           S[1,3]*S[2,2]*S[3,1] -
           S[1,1]*S[2,3]*S[3,2] -
           S[1,2]*S[2,1]*S[3,3]
end

function get_relations(B,C)
  ret = QQMPolyRingElem[]
  for i in 1:3
    for j in i:3
      for k in 1:3
        if i != j && j != k && i != k
          M = hcat(B[:,i], B[:,j], C[:,k])
          push!(ret, determinant(M))
        end
      end
    end
  end
  push!(ret, determinant(C))
  return ret
end

R, UU, WW, z = polynomial_ring(QQ, :U => (1:3, 1:3), :W=> (1:3, 1:3), :z=> 1:binomial(6,3))
U = [i==j ? one(R) : UU[i,j] for i in 1:3, j in 1:3];
W = [i==j ? one(R) : WW[i,j] for i in 1:3, j in 1:3];
A = QQMPolyRingElem[zero(R) -one(R) one(R); one(R) zero(R) -one(R); -one(R) one(R) zero(R)];

F = QQMPolyRingElem[one(R) zero(R) zero(R); zero(R) one(R) zero(R); zero(R) zero(R) one(R)];
#=
using Oscar
R, UU, WW, z = free_associative_algebra(QQ, :U => (1:3, 1:3), :W=> (1:3, 1:3), :z=> 1:binomial(6,3))
U = [i==j ? one(R) : UU[i,j] for i in 1:3, j in 1:3];
W = [i==j ? one(R) : WW[i,j] for i in 1:3, j in 1:3];
A = elem_type(R)[zero(R) -one(R) one(R); one(R) zero(R) -one(R); -one(R) one(R) zero(R)];
F = elem_type(R)[one(R) zero(R) zero(R); zero(R) one(R) zero(R); zero(R) zero(R) one(R)];
UA = U * A
WA = W * A

T = matrix(hcat(F, A, U, UA, W, WA)) ##The actual relization in the end rank 3, 18 elements
T = hcat(F, A, U, UA, W, WA) ##The actual relization in the end rank 3, 18 elements

X1 = hcat(F[:,1],U[:,1],W[:,1]);
X2 = hcat(A[:,1],UA[:,1],WA[:,1]);
X3 = hcat(F[:,2],U[:,2],W[:,2]);
X4 = hcat(A[:,2],UA[:,2],WA[:,2]);
X5 = hcat(F[:,3],U[:,3],W[:,3]);
X6 = hcat(A[:,3],UA[:,3],WA[:,3]);
rels = vcat(get_relations(X1, X2),get_relations(X3, X4),get_relations(X5, X6))
=#

UA = U * A
WA = W * A

T = matrix(hcat(F, A, U, UA, W, WA)) ##The actual relization in the end rank 3, 18 elements
T = hcat(F, A, U, UA, W, WA) ##The actual relization in the end rank 3, 18 elements

UW = hcat(U, W)
#=
M = matroid_from_matrix_columns(T)

n = size(UW, 2)
matrices = []

for i = 1:n-2
    for j = i+1:n-1
        for k = j+1:n
            push!(matrices, UW[:, [i, j, k]])
        end
    end
end

det_relations = QQMPolyRingElem[]
detss = QQMPolyRingElem[]
i = 1;
for M in matrices
  push!(detss, determinant(M))
  push!(det_relations, determinant(M)*z[i] - one(R))
  i += 1;
end

f1 = determinant(hcat(T[:,9], T[:,15], T[:,6]))
f2 = determinant(hcat(T[:,15], T[:,5], T[:,11]))
groebner_basis(ideal([f1,f2]))

=#

function get_det_relsations(UW, z)
    det_relations = QQMPolyRingElem[]
    i = 1;
    n = size(UW, 2)
    for a = 1:n-2
        for b = a+1:n-1
            for c = b+1:n
                M = UW[:, [a, b, c]]
                push!(det_relations, determinant(M)*z[i] - one(R))
                i += 1;
            end
        end
    end
    return det_relations
end

#=
K4 = complete_graph(4)
adj = Int.(collect(adjacency_matrix(K4)))
adj = matrix(adj)
matroid_from_matrix_columns(adj)
=#
#M1_test = load("../M1.mrdi")

X1 = hcat(F[:,1],U[:,1],W[:,1]);
X2 = hcat(A[:,1],UA[:,1],WA[:,1]);
X3 = hcat(F[:,2],U[:,2],W[:,2]);
X4 = hcat(A[:,2],UA[:,2],WA[:,2]);
X5 = hcat(F[:,3],U[:,3],W[:,3]);
X6 = hcat(A[:,3],UA[:,3],WA[:,3]);
rels = vcat(get_relations(X1, X2),get_relations(X3, X4),get_relations(X5, X6))

function compute_elimination_ideal(det_relations, rels, z)
  println("Computing initial Groebner basis...")
  gb = groebner_basis(ideal(rels), algorithm=:f4)
  gb_vect = [gb]
  save("../data/K4/gb_K4_step_0.mrdi", gb_vect[1])
  println("Initial Groebner basis computed and saved.")
  for (i, det_rel) in enumerate(det_relations)
    rels = vcat(collect(gb_vect[end]), det_rel)
    I = ideal(rels)
    println("Computing Groebner basis after adding determinant relation $(i)...")
    groebner_basis(I, algorithm=:f4)
    EI = eliminate(I, [z[i]])
    println("Elimination ideal computed. Computing Groebner basis of the elimination ideal...")
    gb_next = groebner_basis(EI, algorithm=:f4)
    push!(gb_vect, gb_next)  
    save("../data/K4/gb_K4_step_$(i).mrdi", gb_next)
    println("Groebner basis after elimination saved as gb_K4_step_$(i).mrdi")
  end
end

#compute_elimination_ideal(get_det_relsations(UW, z), rels, z)

#=
rels_to_add = [W[3,2]-2, W[1,3]-3, W[2,3]-2, U[2,1]-15, U[3,1]+15, U[1,2]+20, U[2,3]-20, W[3,1]-3, UU[1,1]-1, UU[2,2]-1, UU[3,3]-1, WW[1,1]-1, WW[2,2]-1, WW[3,3]-1]
rels = vcat(rels, rels_to_add)
I = ideal(rels);
groebner_basis(I, algorithm=:f4)
=#

#=
using Oscar
R, UU, WW = polynomial_ring(QQ, :U => (1:3, 1:3), :W=> (1:3, 1:3))
U = [i==j ? one(R) : UU[i,j] for i in 1:3, j in 1:3];
W = [i==j ? one(R) : WW[i,j] for i in 1:3, j in 1:3];
I = ideal([W[2, 3] - 2,
W[1, 3] - 3,
W[3, 2] - 2,
W[2, 1] + W[3, 1],
U[2, 3] - 3*W[3, 1] + 2*W[1, 2] - 7,
U[1, 3] + 3*W[3, 1] - 2*W[1, 2] + 2,
U[3, 2] - 3*W[3, 1] + 2*W[1, 2] - 7,
U[1, 2] + 3*W[3, 1] - 3*W[1, 2] + 5,
U[3, 1] + 2*W[3, 1] - 2*W[1, 2] + 5,
U[2, 1] - 2*W[3, 1] + 2*W[1, 2] - 5,
W[1, 2]^2 - 3*W[3, 1] - 2*W[1, 2] + 1,
W[3, 1]*W[1, 2] - W[1, 2] + 4,
W[3, 1]^2 - 4//3*W[3, 1] + 4//3*W[1, 2] - 7//3,
U[2,1] - 15,
U[3,1] + 15,
U[1,2] + 20,
U[2,3] - 20,
W[3,1] - 3,
UU[1,1] - 1,
UU[2,2] - 1,
UU[3,3] - 1,
WW[1,1] - 1,
WW[2,2] - 1,
WW[3,3] - 1
])
groebner_basis(I, algorithm=:f4)
dim(I) # should be one
real_solutions(I)[1]

rels_to_add = [W[3,2]-2, W[1,3]-3, W[2,3]-2]
rels = vcat(rels, rels_to_add)
I = ideal(rels);
gb = groebner_basis(I, algorithm=:f4)
eliminate(I, [U[3,1], U[2,3]])
=#
#rels = vcat(rels, det_relations)
#=
I = ideal(rels);
gb = groebner_basis(I, algorithm=:f4)
gb_vect = [collect(gb)]
save("gb_K4_step_0.mrdi", gb_vect[1])
i = 1;
for det_rel in det_relations
  rels = vcat(gb_vect[end], det_rel)
  gb_next = groebner_basis(ideal(rels), algorithm=:f4)
  push!(gb_vect, collect(gb_next))  
  save("gb_K4_step_$(i).mrdi", collect(gb_next))
  i += 1;
end

det_relations = get_det_relsations(UW, z) 
gb1 = vcat(collect(gb),det_relations[1])
I = ideal(gb1);
groebner_basis(I,algorithm=:f4);
EI = eliminate(I,[z[1]])
gb_next = groebner_basis(EI,algorithm=:f4)
#do for the rest
    =#
#=
dim(I)
gb = groebner_basis(I);
println("Amount of relations: ", length(gb))
one(R) in gb || println("The ideal does not contain 1")


using Oscar
I1 = ideal(load("../data/K4/gb_K4_step_20.mrdi"))
I2 = ideal(load("../data/K4/gb_K4_step_10.mrdi"))
[ x in I2 for x in gens(I1)]
R = base_ring(I1)
add_rels = [R[15]-2, R[16]-3, R[17]-2]
I3 = I2+ ideal(add_rels)
groebner_basis(I3, algorithm=:f4)
EI = eliminate(I3, [R[i] for i in 15:18])




EI = eliminate(I, [R[i] for i in 1:14])
EI2 = eliminate(EI, [R[18]])

EI2 = EI2 + ideal(add_rels)

f1 = collect(groebner_basis(EI2, algorithm=:f4))[1]
save("../data/K4/eliminated_K4_alot.mrdi", EI2)
save("../data/K4/damn_function.mrdi", f1)

R, (a, b, c, d) = polynomial_ring(QQ, [:a, :b, :c, :d])
f = a^4*b^2*c - a^4*b^2 + a^4*b*c^2 - a^4 *b*c - a^4*b - a^4*c - 2*a^3*b^3*c + 2*a^3*b^3 - 4*a^3*b^2*c^2 + 3*a^3*b^2*c + 2 *a^3*b^2 - 2*a^3*b*c^3 + a^3*b*c^2 + 5*a^3*b*c + 3*a^3*c^2 + a^2*b^4*c - a^2*d^4 + 4*a^2*b^3*c^2 - 2*a^2*b^3*c - 2*a^2*b^3 + 4*a^2*b^2*c^3 - 7*a^2*b^2*c + a^2*b *c^4 + a^2*b*c^3 - 8*a^2*b*c^2 - 3*a^2*c^3 - a*b^4*c^2 + a*b^4 - 2*a*b^3*c^3 - 2 *a*b^3*c^2 + 4*a*b^3*c - a*b^2*c^4 - 3*a*b^2*c^3 + 7*a*b^2*c^2 - a*b*c^4 + 5*a*b*c^3 + a*c^4 + b^4*c^2 - b^4*c + 2*b^3*c^3 - 2*b^3*c^2 + b^2*c^4 - 2*b^2*c ^3 - b*c^4
sols = [[2, 3, 2], [2, 3, 1//2], [2, 3, -3]]

M = load("../computation/M1.mrd")

a = W[3, 2] 
b = W[1, 3]
c = W[2, 3]
 

==


=#




