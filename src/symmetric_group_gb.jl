#Test

export rwel,
  rinj,
  magic_unitary,
  inj,
  wel,
  ip,
  g0,
  indexed_name,
  row_sum,
  col_sum,
  gg,
  g0_named,
  red_row_sum,
  red_col_sum,
  red_sums,
  red_guy,
  rinj_col_sum,
  rwel_col_sum,
  bg,
  g0_count,
  gb_count,
  g1_named,
  g1,
  g1_extended,
  extra_relations

function _index_number(i::Int)
  dgs = reverse(digits(i))
  return join(["₀₁₂₃₄₅₆₇₈₉"[3*d+1] for d in dgs], "") 
end

function _magic_unitary_symbols(n::Int=4)
  u = Matrix{String}(undef, n, n)
  for i in 1:n
    for j in 1:n
      if i > 9 || j > 9
        u[i, j] = "u$(_index_number(j))₋$(_index_number(i))"
      else
        u[i, j] = "u$(_index_number(j))$(_index_number(i))"
      end
    end
  end
  return u
end


##dangerous change to fix to correct order
function magic_unitary(n::Int=4; fancy=true)
  U = [Symbol("u[$(j), $(i)]") for i in 1:n, j in 1:n]
  if fancy 
    U = _magic_unitary_symbols(n)
  end
  _, u = free_associative_algebra(QQ, U)
  return transpose(u)
end

Base.length(A::FreeAssociativeAlgebraElem) = length(A.S)

function magic_unitary(A::FreeAssociativeAlgebra)
  n = Int(sqrt(length(A.S)))
  return reshape([A[i] for i in 1:length(A.S)], (n, n))
end

function magic_unitary(ng::NamedGenerators)
  return magic_unitary(generators(ng))
end


magic_unitary(f::Generic.FreeAssociativeAlgebraElem{T}) where T<:FieldElem = magic_unitary(parent(f))
function magic_unitary(v::Vector{Generic.FreeAssociativeAlgebraElem{T}}) where {T}
  @assert all([parent(x) == parent(v[1]) for x in v]) "All elements must be in the same algebra"
  @assert length(v) > 0 "Empty vector"
  return magic_unitary(parent(v[1]))
end

function rwel(k::Int, j::Int, h::Int=3, v::Int=3; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  n = size(u)[1]
  return sum([u[2, k] * u[s, j] for s in h:n]; init=zero(T)) - sum([u[s, k] * u[1, j] for s in v:n]) + u[1, j] - u[2, k]
end

function rinj(k::Int, j::Int, h::Int=3, v::Int=3; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  n = size(u)[1]
  return sum([u[k, 2] * u[j, s] for s in h:n]) - sum([u[k, s] * u[j, 1] for s in v:n]) + u[j, 1] - u[k, 2]
end

function wel(i::Int, j::Int, k::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  @assert 1 <= i <= size(u)[1] && 1 <= j <= size(u)[2] && 1 <= k <= size(u)[2] "Indices out of bounds"
  return u[i, j] * u[i, k]
end

function inj(i::Int, j::Int, k::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  @assert 1 <= i <= size(u)[1] && 1 <= j <= size(u)[2] && 1 <= k <= size(u)[1] "Indices out of bounds"
  return u[i, j] * u[k, j]
end

function ip(i::Int, j::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  @assert 1 <= i <= size(u)[1] && 1 <= j <= size(u)[2] "Indices out of bounds"
  return u[i, j] * u[i, j] - u[i, j]
end


#=
u = magic_unitary()
f = -4 * u[1,2] * u[2,3] + u[1,2]
normed(f)



=#

row_sum(i::Int, u::Matrix{Generic.FreeAssociativeAlgebraElem{T}} where T<:FieldElem = magic_unitary()) = sum([u[i, x] for x in 1:size(u)[1]]) - one(parent(u[1, 1]))
col_sum(i::Int, u::Matrix{Generic.FreeAssociativeAlgebraElem{T}} where T<:FieldElem =magic_unitary()) = sum([u[x, i] for x in 1:size(u)[1]]) - one(parent(u[1, 1]))

function g0(n::Int=4; names=false)
  ng = g0_named(n)
  if names
    return generators(ng), ng.names
  else
    return generators(ng)
  end
end

function to_dict(v1::Vector{T}, v2::Vector{H}) where {T,H}
  dct = Dict{T,H}()
  @assert length(v1) == length(v2)
  for i in eachindex(v1)
    dct[v1[i]] = v2[i]
  end
  return dct
end

function to_dict(v1::Vector{T}, v2::Vector{H}, dct::Dict{T,H}) where {T,H}
  @assert length(v1) == length(v2)
  for i in eachindex(v1)
    @assert !haskey(dct,v1[i]) "dct has this key already"
    dct[v1[i]] = v2[i]
  end
  return dct
end


function merge_dct(d1::Dict{T,H}, d2::Dict{T,H}) where {T,H}
    ans = Dict{T,H}
    for key in keys(d1)
       @assert !haskey(d2,key)
       ans[key] = d1[key]
    end
    for key in keys(d2)
       @assert !haskey(d1,key)
       ans[key] = d2[key]
    end
end

function g0_named(n::Int=4; u=-1)
  if u == -1
    u = magic_unitary(n)
  end

  cs = [col_sum(i, u) for i in 1:n]
  cs_names = indexed_name("cs", 1:n)
  cs_ids = [Symbol("cs$i") for i in 1:n]
  ng = named_generators(cs, cs_names, cs_ids)  

  rs = [row_sum(i, u) for i in 2:n]
  rs_names = indexed_name("rs", 2:n)
  rs_ids = [Symbol("rs$i") for i in 2:n]
  add!(ng, rs, rs_names, rs_ids)

  #Idempotent relations but not the ones that contain i,j = 1
  ips = [ip(i,j; u=u) for i in 2:n for j in 2:n]
  ip_names = indexed_name("ip", [parse(Int, "$i$j") for i in 2:n for j in 2:n])
  ip_ids = [Symbol("ip$i$j") for i in 2:n for j in 2:n]
  add!(ng, ips, ip_names, ip_ids)

  wels = [wel(i,j,k;u=u) for i in 2:n for j in 2:n for k in 2:n if j != k]
  wels_names = indexed_name("wel", [parse(Int, "$i$j$k") for i in 2:n for j in 2:n for k in 2:n if j != k])
  wels_ids = [Symbol("wel$i$j$k") for i in 2:n for j in 2:n for k in 2:n if j != k]
  add!(ng, wels, wels_names, wels_ids)

  injs = [inj(i,j,k; u=u) for i in 2:n for j in 2:n for k in 2:n if i != k]
  inj_names = indexed_name("inj", [parse(Int, "$i$j$k") for i in 2:n for j in 2:n for k in 2:n if i != k])
  inj_ids = [Symbol("inj$i$j$k") for i in 2:n for j in 2:n for k in 2:n if i != k]
  add!(ng, injs, inj_names, inj_ids)

  rwels = [rwel(k, j; u=u) for j in 2:n for k in 2:n if  k != j &&!(j == 3 && k == 2)]
  rwels_names = indexed_name("rwel", [parse(Int, "$k$j") for j in 2:n for k in 2:n if k != j && !(j == 3 && k == 2)])
  rwels_ids = [Symbol("rwel$k$j") for j in 2:n for k in 2:n if k != j && !(j == 3 && k == 2)]
  add!(ng, rwels, rwels_names, rwels_ids)

  rinjs = [rinj(k, j; u=u) for j in 2:n for k in 2:n if k != j]
  rinjs_names = indexed_name("rinj", [parse(Int, "$k$j") for j in 2:n for k in 2:n if k != j])
  rinjs_ids = [Symbol("rinj$k$j") for j in 2:n for k in 2:n if k != j]
  add!(ng, rinjs, rinjs_names, rinjs_ids)

  return ng
end



function gg(x::Int, y::Int, u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  n = size(u)[1]
  gg_base = u[x, y] * (sum([row_sum(i, u) for i in 2:n if i != x]) - sum([col_sum(i, u) for i in 2:n if i != y]))
  gg_plus = sum([wel(x, y, i; u=u) for i in 2:n if i != y]) - sum([inj(x, y, i; u=u) for i in 2:n if i != x])
  return gg_base + gg_plus
end

function indexed_name(name::String, numbers::Matrix{Int})
  numbers = vcat(numbers...)
  return indexed_name(name, numbers)
end

function indexed_name(name::String, numbers::UnitRange{Int})
  indexed_name(name, collect(numbers))
end

function indexed_name(name::String, numbers::Vector{Int})
  return [name * join(["₀₁₂₃₄₅₆₇₈₉"[3*i+1] for i in reverse(digits(n))], "") for n in numbers]
end

function red_row_sum(x::Int, y::Int, k::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  return u[x, y] * row_sum(k, u) - inj(x, y, k; u)
end
function red_col_sum(x::Int, y::Int, k::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  return u[x, y] * col_sum(k, u) - wel(x, y, k; u)
end

function red_sums(u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  n = size(u)[1]
  rrs = [sum([red_row_sum(i, j, k; u) for k in 2:n if i != k]) for i in 2:n for j in 2:n]
  rcs = [sum([red_col_sum(i, j, k; u) for k in 2:n if j != k]) for i in 2:n for j in 2:n]
  return vcat(rrs, rcs)
end

function red_guy(x::Int, y::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  n = size(u)[1]
  return sum([rinj(k, y; u) for k in 2:n if k != y]) - sum([red_row_sum(y, x, k; u) for k in 2:n if k != y])
end

function rinj_col_sum(x::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  n = size(u)[1]
  return sum([rinj(k, x; u) for k in 2:n if k != x])
end

function rwel_col_sum(x::Int; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T}
  n = size(u)[1]
  return sum([rwel(k, x; u) for k in 2:n if k != x])
end


function extra_relations(u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where {T} 
    n = size(u)[1]
    
    ng =  named_generators(typeof(u[1])[], String[], Symbol[])

    ggs = [gg(i, j, u) for i in 2:n for j in 2:n]
    ggs_names = indexed_name("gg", reshape([parse(Int, "$i$j") for i in 2:n, j in 2:n], (n - 1)^2))
    ggs_ids = [Symbol("gg$j$i") for i in 2:n for j in 2:n]
    add!(ng, ggs, ggs_names, ggs_ids)

    red_sums_v = red_sums(u)
    red_rows_names = indexed_name("rrs", [parse(Int, "$i$j") for i in 2:n for j in 2:n])
    red_cols_names = indexed_name("rcs", [parse(Int, "$i$j") for i in 2:n for j in 2:n])
    red_rows_ids = [Symbol("rrs$i$j") for i in 2:n for j in 2:n]
    red_cols_ids = [Symbol("rcs$i$j") for i in 2:n for j in 2:n]
    add!(ng, red_sums_v, vcat(red_rows_names, red_cols_names), vcat(red_rows_ids, red_cols_ids))


    rinj_wel_col_sums = vcat([rinj_col_sum(i; u) for i in 2:n], [rwel_col_sum(i; u) for i in 2:n if i ≠ 3])
    rinj_wel_col_sums_names = vcat(indexed_name("rinjcs", 2:n), indexed_name("rwelcs", [i for i in 2:n if i ≠ 3]))
    rinj_wel_col_sums_ids = vcat([Symbol("rinjcs$i") for i in 2:n],[Symbol("rwelcs$i") for i in 2:n if i ≠ 3])
    add!(ng, rinj_wel_col_sums, rinj_wel_col_sums_names, rinj_wel_col_sums_ids)

    check_integrity(ng)
    return ng
end


#=
using Oscar
G0, names = g0(4,names=true)
u = magic_unitary(G0)
bg1 = rwel(2,3; u = u)
normal_form(bg1,G0)
names

G0, names = g0_extended(6,names=true)
u = magic_unitary(G0)
bg1 = rwel(2,3; u = u)
normal_form(bg1,G0)
names

mrrs = mod_rrs(2,3; u = u)

r, v = normal_form_with_rep(mrrs,G0);
r != 0 && error("r != 0");
x1 = reps_vector_to_poly(v,names);
print(x1)

digits(5)
indexed_name("test", [2,4,5,15])

groebner_basis(gb1)
AbstractAlgebra.interreduce!(gb1)


max_degree(gb!)


=#


function bg(z::Int, k::Int, j::Int, i::Union{Int, Missing}=missing; u::Matrix{Generic.FreeAssociativeAlgebraElem{T}}=magic_unitary()) where T<:FieldElem
z == 1 && !ismissing(i) && return inj(k, 2, j, u=u) * u[i, 3] - u[k, 2] * rinj(j, i, u=u) #
z == 2 && !ismissing(i) && return u[k, 2] * inj(j, 3, i, u=u) - rinj(k, j, u=u) * u[i, 3] #
z == 3 && ismissing(i) &&  return ip(2, k, u=u) * u[3, j] - u[2, k] * rwel(k, j, u=u) #
z == 4 && ismissing(i) && return u[2, k] * ip(3, j, u=u) - rwel(k, j, u=u) * u[3, j] #
z == 5 && ismissing(i) && return ip(k, 2, u=u) * u[j, 3] - u[k, 2] * rinj(k, j, u=u) #
z == 6 && ismissing(i) && return u[k, 2] * ip(3, j, u=u) - rinj(k, j, u=u) * u[3, j] #
z == 7 && !ismissing(i) && return wel(2, k, j, u=u) * u[3, i] - u[2, k] * rwel(j, i, u=u)
z == 8 && !ismissing(i) && return u[2, k] * wel(3, j, i, u=u) - rwel(k, j, u=u) * u[3, i]
z == 9 &&  ismissing(i) && return rinj(k, 2, u=u) * u[3, j] - u[k, 2] * rwel(3, j, u=u)
z == 10 && ismissing(i) && return u[2, k] * rinj(3, j, u=u) - rwel(k, 2, u=u) * u[j, 3] #
z == 11 && !ismissing(i) && return inj(k, j, 2, u=u) * u[3, i] - u[k, j] * rwel(j, i, u=u) #
z == 12 && !ismissing(i) && return u[2, k] * inj(3, j, i, u=u) - rwel(k, j, u=u) * u[i, j]
z == 13 && !ismissing(i) && return wel(k, j, 2, u=u) * u[i, 3] - u[k, j] * rinj(k, i, u=u)
z == 14 && !ismissing(i) && return u[k, 2] * wel(j, 3, i, u=u) - rinj(k, j, u=u) * u[j, i]

ismissing(i) && @warn "k is required for z = 1, 2, 7, 8, 11, 12, 13, 14"
!ismissing(i) && @warn " k must be missing for z = 3, 4, 5, 6, 9, 10"
throw(ArgumentError("You have done something wrong"))
end

function g0_count(n::Int)
  return 2n^3 -5n^2 +4n - 1
end

function gb_count(n::Int)
  return 2*(n-2)*(n-3)*(n-1) + 2*(n-4)*(n-2)+2*(n-3)+1 + g0_count(n)
end

function g1_named(n::Int; u=-1)
  ng= g0_named(n, u=u)  
  u = magic_unitary(ng)

  e1 = [bg(2,k,j,i;u=u) for k=3:n for j=3:n for i=2:n if i!=j && j!=k]
  e1_names = indexed_name("bg2_", [parse(Int, "$k$j$i") for k=3:n for j=3:n for i=2:n if i!=j && j!=k])
  e1_ids = [Symbol("bg2_$k$j$i") for k=3:n for j=3:n for i=2:n if i!=j && j!=k]
  add!(ng, e1, e1_names, e1_ids)

  e1_s = [bg(8,k,j,i;u=u) for k=3:n for j=3:n for i=2:n if i!=j && j!=k]
  e1_s_names = indexed_name("bg8_", [parse(Int, "$k$j$i") for k=3:n for j=3:n for i=2:n if i!=j && j!=k])
  e1_s_ids = [Symbol("bg8_$k$j$i") for k=3:n for j=3:n for i=2:n if i!=j && j!=k] 
  add!(ng, e1_s, e1_s_names, e1_s_ids)
  
  e2 = [bg(2,k,2,i;u=u) for k=3:n for i=4:n]
  e2_names = indexed_name("bg2_", [parse(Int, "$(k)2$i") for k=3:n for i=4:n])
  e2_ids = [Symbol("bg2_$(k)2$i") for k=3:n for i=4:n]
  add!(ng, e2, e2_names, e2_ids)

  e2_s = [bg(8,k,2,i;u=u) for k=3:n for i=4:n]
  e2_s_names = indexed_name("bg8_", [parse(Int, "$(k)2$i") for k=3:n for i=4:n])
  e2_s_ids = [Symbol("bg8_$(k)2$i") for k=3:n for i=4:n]
  add!(ng, e2_s, e2_s_names, e2_s_ids)

  e3 = [bg(2,2,j,i;u=u) for j in 5:n for i in 2:n if j!=i]
  e3_names = indexed_name("bg2_", [parse(Int, "2$j$i") for j in 5:n for i in 2:n if j!=i])
  e3_ids = [Symbol("bg2_2$j$i") for j in 5:n for i in 2:n if j!=i]
  add!(ng, e3, e3_names, e3_ids)
  
  e3_s = [bg(8,2,j,i;u=u) for j in 5:n for i in 2:n if j!=i]
  e3_s_names = indexed_name("bg8_", [parse(Int, "2$j$i") for j in 5:n for i in 2:n if j!=i])
  e3_s_ids = [Symbol("bg8_2$j$i") for j in 5:n for i in 2:n if j!=i]
  add!(ng, e3_s, e3_s_names, e3_s_ids)

  e4 = [bg(2,2,4,i;u=u) for i in 2:n if 4!=i && 3!=i]
  e4_names = indexed_name("bg2_", [parse(Int, "24$i") for i in 2:n if 4!=i && 3!=i])
  e4_ids = [Symbol("bg2_24$i") for i in 2:n if 4!=i && 3!=i]
  add!(ng, e4, e4_names, e4_ids)

  e4_s = [bg(8,2,4,i;u=u) for i in 2:n if 4!=i && 3!=i]
  e4_s_names = indexed_name("bg8_", [parse(Int, "24$i") for i in 2:n if 4!=i && 3!=i])
  e4_s_ids = [Symbol("bg8_24$i") for i in 2:n if 4!=i && 3!=i]
  add!(ng, e4_s, e4_s_names, e4_s_ids) 

  e5 = [bg(2,2,4,3;u=u)]
  e5_names = ["bg2_243"]
  e5_ids = [Symbol("bg2_243")]
  add!(ng, e5, e5_names, e5_ids)
  
  @assert length(ng) == gb_count(n) "Something went wrong: $(length(ng)) != $(gb_count(n))"
  check_integrity(ng)
  return ng
end

function g1(n::Int, names=false)
  ng = g1_named(n)
  if names
    return generators(ng), ng.names
  else
    return generators(ng)
  end
end

function g1_extended(n::Int)
  ng = g1_named(n)
end


function g00_named(n::Int=4; u=-1)
  if u == -1
    u = magic_unitary(n)
  end

  cs = [col_sum(i, u) for i in 1:n]
  cs_names = indexed_name("cs", 1:n)
  cs_ids = [Symbol("cs$i") for i in 1:n]
  ng = named_generators(cs, cs_names, cs_ids)  

  rs = [row_sum(i, u) for i in 1:n]
  rs_names = indexed_name("rs", 1:n)
  rs_ids = [Symbol("rs$i") for i in 1:n]
  add!(ng, rs, rs_names, rs_ids)

  #Idempotent relations but not the ones that contain i,j = 1
  ips = [ip(i,j; u=u) for i in 1:n for j in 1:n]
  ip_names = indexed_name("ip", [parse(Int, "$i$j") for i in 1:n for j in 1:n])
  ip_ids = [Symbol("ip$i$j") for i in 1:n for j in 1:n]
  add!(ng, ips, ip_names, ip_ids)
  
  return ng
end
