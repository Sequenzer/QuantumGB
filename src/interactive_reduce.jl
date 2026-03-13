
using Oscar.AbstractAlgebra.Generic

export reps_vector_to_poly, reduction_string



"""
```jldoctest
using Oscar
R, (x, y) = free_associative_algebra(QQ, ["x", "y"]);
f = 2x^2 + 3x*y*x^2 + 4y^2;
g = [x^2, y^2, x*y];

zr,  dct = normal_form_with_rep(f, g);
reps_vector_to_poly(dct)
# output

Dict{AbstractAlgebra.Generic.FreeAssociativeAlgebraElem, AbstractAlgebra.Generic.FreeAssociativeAlgebraElem{QQFi
eldElem}} with 2 entries:
  x^2 => 2*x^2
  y^2 => 4*y^2
```

"""
function reps_vector_to_poly(v::Vector)
  length(v) == 0 && return 0
  A = parent(v[1][3])
  f = zero(A)
  for rep in v
    f += rep[1] * rep[2] * rep[3] * rep[4]
  end
  return f
end
"""
```jldoctest
using Oscar
R, (x, y) = free_associative_algebra(QQ, ["x", "y"]);
f = 2x^2 + 3x*y*x^2 + 4y^2;
g = [x^2, y^2, x*y];
names = Dict(x^2 => "u", y^2 => "v", x*y => "w")

zr,  dct = normal_form_with_rep(f, g);
reps_vector_to_poly(dct, names)
# output

Dict{AbstractAlgebra.Generic.FreeAssociativeAlgebraElem, AbstractAlgebra.Generic.FreeAssociativeAlgebraElem{QQFi
eldElem}} with 2 entries:
  x^2 => 2*x^2
  y^2 => 4*y^2
```

"""
function reps_vector_to_poly(v::Vector, names::Dict{<:Generic.FreeAssociativeAlgebraElem,String})
  v3 = [x[3] for x in v]
  @assert all([x in keys(names) for x in v3])
  length(v) == 0 && return 0
  f = ""
  A = parent(v[1][3])
  for rep in v
    if rep[1] != one(A)
      f *= string(rep[1])
      f *= "*"
    end
    if rep[2] != one(A) 
      f *= string(rep[2]) 
      f *= "*"
    end
    f *= names[rep[3]] 
    if rep[4] != one(A) 
      f *= "*"
      f *= string(rep[4])
    end
    f *= " + "
  end
return f[1:end-2]
end

function reduction_string(
  g1::NamedGenerators,
  ele::Generic.FreeAssociativeAlgebraElem;
  extra::Union{NamedGenerators, Nothing} = nothing,
  to_file::String = "",
  len::Int=-1,
  debug::Bool=false,
  words::Vector{String} = String[])

  G1, names = generators(g1), g1.names
  


  if !isnothing(extra)
    extra_gens, extra_names = generators(extra), extra.names
    r,v = normal_form_with_rep(ele, extra_gens)

    if iszero(r) 
      @warn "Reduced to zero using only the extra generators"
      return reps_vector_to_poly(v, extra_names)
    end
    y = reps_vector_to_poly(v, extra_names)
    println(y)
  else
    y = ""
  end

  r, v = normal_form_with_rep(ele,G1, len)



  if debug
    @info "The reduction required $(length(v)) steps."
    println()
  end
  len==-1 && r != 0 && @warn "This does not reduce to zero, using the normal_form algorithm"

  if words != []
    filter!(x -> replace(g1.names[x[3]], r"[^a-zA-Z]" => "") in words,v)
  end
  x = reps_vector_to_poly(v,names)
  
  if y == ""
    x = x
  else
    x = x * " + " * y
  end
  
  if to_file != ""
    open(to_file, "w") do io
        println(io, x)
    end
  end
  return x
end



#= Reduction of rwel23
n = 8
G1 = g1_named(n)
u = magic_unitary(n)
E1 = extra_relations(u)
QuantumGB.add!(E1, G1)
rwel23 = rwel(2,3; u=u)


reduction_string(E1, rwel23; words=["rinjcs","rwel"],len=20)

g1 = generators(G1)
r, v = normal_form_with_rep(rwel23,g1,-1)
as = ["rinj","rwel"]

G1.names[v[1][3]]

rwel23 = rwel(2,3; u=u)
reduction_string(E1, rwel23)
reduction_string(E1, rwel23; to_file="../data/reduction_strings/n_8_rwel23.txt")
=#

#= Trying todo the same with bg(9,v,h) for v = 5, h = 6
n = 6
G1 = g1_named(n)
u = magic_unitary(n)

#Thing to reduce
v = 5
h = 6
bege9 = bg(9,v,h; u=u)

using Base.Iterators

[(i, j) for (i, j) in Iterators.product(2:n, 2:n)]


n = 6
G1 = g1_named(n)
u = magic_unitary(n)
bege8243 = bg(8,2,4,3; u=u)
reduction_string(G1,bege8243; debug=true)

wesc_iterators = [(i,j,k,t) for i = 2:n for j = 2:n for k = 2:n for t in 1:n if j != k];
wesc = [G1["wel$(i)$(j)$(k)"]*u[1,t] for (i,j,k,t) in wesc_iterators];
wesc_names = indexed_name("wesc", [parse(Int, "$i$j$k$t") for (i,j,k,t) in wesc_iterators]);
wesc_ids = [Symbol("wesc$i$j$k$t") for (i,j,k,t) in wesc_iterators];

iesc_iterators = [(i,j,k,t) for i = 2:n for j = 2:n for k = 2:n for t in 1:n if i != k];
iesc = [G1["inj$(i)$(j)$(k)"]*u[t,1] for (i,j,k,t) in iesc_iterators];
iesc_names = indexed_name("iesc", [parse(Int, "$i$j$k$t") for (i,j,k,t) in iesc_iterators]);
iesc_ids = [Symbol("iesc$i$j$k$t") for (i,j,k,t) in iesc_iterators];

uucs_iterators = [(i,j,k,h,f) for i = 1:n for j = 1:n for k = 2:n for h = 2:n for f = 2:n if i != k && j != h && f !=h];
uucs = [u[i,j]*u[k,h]*G1["cs$f"]-u[i,j]*G1["wel$(k)$(h)$(f)"] for (i,j,k,h,f) in uucs_iterators];
uucs_names = indexed_name("uucs", [parse(Int, "$i$j$k$h$f") for (i,j,k,h,f) in uucs_iterators]);
uucs_ids = [Symbol("uucs$i$j$k$h$f") for (i,j,k,h,f) in uucs_iterators];

uurs_iterators = [(i,j,k,h,f) for i = 2:n for j = 2:n for k = 2:n for h = 2:n for f = 2:n if i != k && j != h && f !=k];
uurs = [u[i,j]*u[k,h]*G1["rs$f"]-u[i,j]*G1["inj$(k)$(h)$(f)"] for (i,j,k,h,f) in uurs_iterators];
uurs_names = indexed_name("uurs", [parse(Int, "$i$j$k$h$f") for (i,j,k,h,f) in uurs_iterators]);
uurs_ids = [Symbol("uurs$i$j$k$h$f") for (i,j,k,h,f) in uurs_iterators];

ursu_iterators = [(i,j,k,h,f) for i = 2:n for j = 2:n for k = 2:n for h = 2:n for f = 2:n if i != k && k != h];
ursu = [u[i,j]*G1["rs$k"]*u[h,f] - u[i,j]*G1["inj$(k)$(f)$(h)"] - G1["inj$(i)$(j)$(k)"]*u[h,f] for (i,j,k,h,f) in ursu_iterators];
ursu_names = indexed_name("ursu", [parse(Int, "$i$j$k$h$f") for (i,j,k,h,f) in ursu_iterators]);
ursu_ids = [Symbol("ursu$i$j$k$h$f") for (i,j,k,h,f) in ursu_iterators];

ucsu_iterators = [(i,j,k,h,f) for i = 2:n for j = 2:n for k = 2:n for h = 2:n for f = 2:n if k !=j && f != k];
ucsu = [u[i,j]*G1["cs$k"]*u[h,f] - u[i,j]*G1["wel$(h)$(k)$(f)"] - G1["wel$(i)$(j)$(k)"]*u[h,f] for (i,j,k,h,f) in ucsu_iterators];
ucsu_names = indexed_name("ucsu", [parse(Int, "$i$j$k$h$f") for (i,j,k,h,f) in ucsu_iterators]);
ucsu_ids = [Symbol("ucsu$i$j$k$h$f") for (i,j,k,h,f) in ucsu_iterators];

bg2sr_iterators = [(i,j) for i = 2:n for j = 2:n if i != j && (i,j) != (2,3)];
bg2sr = [sum([G1["bg2_$(i)$(j)$(k)"] for k in 2:n if k != j && (j,k) != (2,3)]) for (i,j) in bg2sr_iterators];
bg2sr_names = indexed_name("bg2sr", [parse(Int, "$i$j") for (i,j) in bg2sr_iterators]);
bg2sr_ids = [Symbol("bg2sr$i$j") for (i,j) in bg2sr_iterators];

function help1(i,j)
  ans = -sum([E1["ucsu$(i)$(j)$(k)$(3)$(3)"] for k in 4:n])
  ans += sum([sum([E1["uucs$(i)$(j)$(k)$(h)$(3)"] for h in 4:n]) for k in 3:n if k != i])
  ans += sum([u[i,j]*E1["rwel$(k)$(3)"] for k in 4:n])
  ans += sum([E1["wesc$(i)$(j)$(k)$(3)"] for k in 4:n])
  ans += sum([E1["bg2sr$(i)$(k)"] for k in 2:n if k != i])
  ans -= sum([E1["bg2_$(i)$(k)3"] for k in 4:n if k != i])
  return ans
end



E1 = named_generators(wesc, wesc_names, wesc_ids)
add!(E1, iesc, iesc_names, iesc_ids)
add!(E1, uucs, uucs_names, uucs_ids)
add!(E1, uurs, uurs_names, uurs_ids)
add!(E1, ursu, ursu_names, ursu_ids)
add!(E1, ucsu, ucsu_names, ucsu_ids)
add!(E1, bg2sr, bg2sr_names, bg2sr_ids)
add!(E1, G1; check=false)

reduction_string(E1, bege8243
-sum([E1["bg2_2$(k)3"] for k in 4:n])+sum([E1["bg8_2$(k)3"] for k in 5:n])
-u[3,2]*E1["cs4"]*u[3,3] +u[3,2]*E1["rwel43"]+E1["wel324"]*u[3,3]
+help1(3,2)-u[3,2]*E1["rwel43"]+E1["ucsu32433"]-E1["wel325"]*u[3,3] - E1["wel326"]*u[3,3] #Scheinbar nicht fine enough
+help1(4,2)+help1(5,2)+help1(6,2)
,len=40)
)
+E1["bg2sr32"]
;len=30)
,to_file="../data/reduction_strings/n_6_bege8243.txt")


row_sum(1,u)
reduction_string(G1, row_sum(1,u))

rwel uucs uucs 

ucsu₅₂₄₃₃ + -1*u₅₂*rwel₄₃ + -1*bg2sr₅₂ + -1*uucs₅₂₃₄₃ + -1*bg2sr₅₃ + -1*uucs₅₂₄₄₃ + -1*bg2sr₅₄ + bg2_₅₄₃ + -1*wesc₅₂₄₃ + -1*uucs₅₂₆₄₃ + -1*bg2sr₅₆ + bg2_₅₆₃ + ucsu₅₂₅₃₃ +

ucsu₆₂₄₃₃ + -1*u₆₂*rwel₄₃ + -1*bg2sr₆₂ + -1*uucs₆₂₃₄₃ + -1*bg2sr₆₃ + -1*uucs₆₂₄₄₃ + -1*bg2sr₆₄ + bg2_₆₄₃ + -1*uucs₆₂₅₄₃ + -1*bg2sr₆₅ + bg2_₆₅₃ + -1*wesc₆₂₄₃ + ucsu₆₂₅₃₃ +

-1*u₅₂*rwel₅₃ + -1*uucs₅₂₃₅₃ + -1*uucs₅₂₄₅₃ + -1*wesc₅₂₅₃ + -1*uucs₅₂₆₅₃ + ucsu₅₂₆₃₃ + -1*u₅₂*rwel₆₃ + -1*uucs₅₂₃₆₃ + -1*uucs₅₂₄₆₃ + -1*wesc₅₂₆₃ + -1*uucs₅₂₆₆₃ +

-1*u₆₂*rwel₅₃ + -1*uucs₆₂₃₅₃ + -1*uucs₆₂₄₅₃ + -1*uucs₆₂₅₅₃ + -1*wesc₆₂₅₃ + ucsu₆₂₆₃₃ + -1*u₆₂*rwel₆₃ + -1*uucs₆₂₃₆₃ + -1*uucs₆₂₄₆₃ + -1*uucs₆₂₅₆₃ + -1*wesc₆₂₆₃ +



#Define helper:
rrcs = [u[5,2]*u[k,j]*G1["cs6"]-u[5,2]*G1["wel$(k)$(j)6"] for k in 3:n if k != 5 for j in 3:n if j != 6]
rrcs_names = indexed_name("rrcs", [parse(Int, "$k$j") for k = 3:n if k != 5 for j = 3:n if j != 6])
rrcs_ids = [Symbol("rrcs$k$j") for k = 3:n if k != 5 for j = 3:n if j != 6]
E1 = named_generators(rrcs, rrcs_names, rrcs_ids)

swel = [G1["wel5$k$j"]*u[1,6] for j in 3:n for k in 3:n if k != j]
swel_names = indexed_name("swel", [parse(Int, "$k$j") for j = 3:n for k = 3:n if k != j])
swel_ids = [Symbol("swel$k$j") for j = 3:n for k = 3:n if k != j]
add!(E1, swel, swel_names, swel_ids)


es = [ sum([rinj(v,k; u=u) * u[i,h]  for i in 2:n if i!=k]) for k = 2:n if k != v];
es_names = indexed_name("es", [parse(Int, "$k") for k = 2:n if k != v])
es_ids = [Symbol("es$k") for k in 2:n if k != v]
add!(E1, es, es_names, es_ids)

add!(E1, G1; check=false)



rrrcs = [sum([E1["rrcs$(k)$(j)"]-E1["es$k"] + G1["wel52$k"]*u[1,6] for k in 3:n if k != 5]) for j in 3:n if j != 6]
rrrcs_names = indexed_name("rrrcs", [parse(Int, "$j") for j in 3:n if j != 6])
rrrcs_ids = [Symbol("rrrcs$j") for j in 3:n if j != 6]
E2 = named_generators(rrrcs, rrrcs_names, rrrcs_ids)
add!(E2, E1)


reduction_string(E2, bege9)
reduction_string(G1, bege9; to_file="../data/reduction_strings/n_6_bege9.txt")

reduction_string(E2, bege9 +
sum([G1["rinj52"]*u[j,6] for j in 4:n])
  -E1["rrcs33"] + E1["es3"] - E1["rrcs43"] + E1["es4"] - E1["wel523"]*u[1,6]
  -E1["rrcs63"] + E1["es6"] 
)
; to_file="../data/reduction_strings/n_6_bege9.txt")
=#


#=Those are useless (lemma 12)
iter = [(a,k,j,x,y) for a = 2:n for k = 2:n for j = 2:n for x = 3:n for y = 3:n if a != k && k!= j];
srinj = [u[a,2] * rinj(k,j,x,;u=u) for (a,k,j,x,y) in iter];
srinj_names = indexed_name("srinj", [parse(Int, "$a$k$j$x$y") for (a,k,j,x,y) in iter]);
srinj_ids = [Symbol("srinj$a$k$j$x$y") for (a,k,j,x,y) in iter];
add!(E1, srinj, srinj_names, srinj_ids)



#Checking on commutators
#First check if the gb is correct
I0 = quantum_symmetric_group(5)
u = magic_unitary(I0.gens[1])
G1 = g1_named(5,u=u)
G1b = G1.gs
I1 = ideal(G1b)
I1.gb = I1.gens




groebner_basis(I0)


is_subset(I0, I1)
is_subset(I1,I0)

IC = g1_named(5,u=u)
srinj = [u[4,5]*u[3,3] - u[3,3]*u[4,5]];
srinj_names = indexed_name("srinj", [parse(Int, "$a$k$j$x$y") for (a,k,j,x,y) in iter]);
srinj_ids = [Symbol("srinj$a$k$j$x$y") for (a,k,j,x,y) in iter];
add!(E1, srinj, srinj_names, srinj_ids)

comm1 = u[4,5]*u[3,3] - u[3,3]*u[4,5]

n = 5
S = quantum_symmetric_group(5)
R = base_ring(S)
G1 = groebner_basis(gens(S),algorithm=:buchberger)
f = R[4]*R[3] - R[3]*R[4]
normal_form(f, G1)
rem = []
zeros = []
for (i,j) in Iterators.product(1:n^2, 1:n^2)
  f = R[i]*R[j] - R[j]*R[i]
  r,v = normal_form_with_rep(f, G1)
  if !iszero(r)
    push!(rem, f)
  else
    push!(zeros, f)
  end
end



=#
