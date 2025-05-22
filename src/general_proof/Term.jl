#Defines the Term structure

export Term,
  create_preimage_in,
  replace_with!,
  filter_index


mutable struct Term
  L::Lexicon
  pairs::Vector{Tuple{RingElem,Int}}
  function Term(L::Lexicon, pairs::Vector{Tuple{RingElem,Int}})
    @assert (all(x->x[2] <= length(L.predicates), pairs)) "Index out of bounds"
    @assert (all(x->parent(x[1]) == L.coefficient_ring, pairs)) "Coefficents not in the coefficient ring"
    new(L, pairs)
  end
  Term(L::Lexicon) = new(L, [])
end

function Base.push!(t::Term, x::Tuple{RingElem,Int})
  @assert x[2] <= length(t.L.predicates) "Index out of bounds"
  @assert parent(x[1]) == t.L.coefficient_ring "Coefficient not in the coefficient ring"
  push!(t.pairs, x)
end

Base.iszero(t::Term) = isempty(t.pairs)

function Base.show(io::IO, t::Term)
  if iszero(t)
    println("Zero term")
    return
  end

  rev_dct = reverse_dict(t.L.labels)
  ret = map(x->(x[1], [rev_dct[y] for y in t.L.predicates[x[2]]]), t.pairs) 
  println("Term over lexicon with $(length(t.L.predicates)) predicates:")
  show(io, "text/plain", ret)
end

function create_preimage_in(L::Lexicon, v::Vector{Vector{Any}}, coeff::RingElem; filter::Vector = [])
  v = Vector{String}[string.(x) for x in v]
  s = Iterators.product(v...) # ("str", "str", "str")...
  labels = L.labels
  P = Vector{Int}[]
  for (i, j) in filter
    if j > i
      i, j = j, i
    end
    s = Iterators.filter(x -> x[i] == "g"  || x[j] == "g" || x[i] != x[j], s)
  end 

  for x in s
    x = collect(x) 
    for (i, j) in filter
      if x[j] == "g" && x[i] == "g"
        x[i] = "g⩓≠i$(j)"
      end
    end
    push!(P, [labels[y] for y in x])
  end

  vec = Term(L)
  R = L.coefficient_ring
  for x in P  
    idx = find(L, x)
    @assert !isnothing(idx) "$x not found in Lexicon"
    push!(vec, (R(coeff), idx))
  end
  return vec
end

function create_preimage_in(L::Lexicon, v::Vector{Vector{Any}}, coeff::Number; filter::Vector = [])
  R = L.coefficient_ring
  coeff = R(coeff)
  return create_preimage_in(L, v, coeff, filter=filter)
end

function create_preimage_in(L::Lexicon, v::Vector{Vector}, coeff::RingElem; filter::Vector = [])
  v = Vector{Any}[string.(x) for x in v]
  return create_preimage_in(L, v, coeff, filter=filter)
end

function create_preimage_in(L::Lexicon, v::Vector{Vector}, coeff::Number; filter::Vector = [])
  R = L.coefficient_ring
  coeff = R(coeff)
  return create_preimage_in(L, v, coeff, filter=filter)
end

"""
  
Example:
```julia
L1 = lexicon([[1],[2],[3],["g"]])
L2 = lexicon([[1],[2],["g"],[3]])

L = L1 * L2
s1 = create_preimage_in(L, [[2,3,:g],[2,3,:g]], 1);
d1 = create_preimage_in(L, [[2,3,:g],[3,:g]], -1);
s1+d1 #Should delete most.


```

"""
function Base.:+(t1::Term, t2::Term)
  @assert t1.L == t2.L "Lexicons do not match"
    new_pairs = copy(t1.pairs)
  for x in t2.pairs
    i = findfirst(y->y[2] == x[2], new_pairs)
    if isnothing(i)
      push!(new_pairs, x)
    else
      if new_pairs[i][1] + x[1] == 0
        deleteat!(new_pairs, i)
      else
        new_pairs[i] = (new_pairs[i][1] + x[1], new_pairs[i][2])
      end
    end
  end
  return Term(t1.L, new_pairs)
end

"""
  
Example:
```julia
L1 = lexicon([[1],[2],[3],["g"]])
L2 = lexicon([[1],[2],["g"],[4]])

L = L1 * L2
s1 = create_preimage_in(L, [[2,3,:g],[2,4,:g]], 1);
d1 = create_preimage_in(L, [[2,3,:g],[2,:g]], -1);
s1+d1 #Should delete most.

t1 = create_preimage_in(L1,[[2,:g]],1)
t2 = create_preimage_in(L2,[[2,:g]],1)
L_new = (t1*t2).L
L_new == L

vnew  = vcat(L.predicates[s1.pairs[1][2]],L.predicates[d1.pairs[1][2]])
```
"""
function Base.:*(t1::Term, t2::Term)
    new_lex = t1.L * t2.L
    new_pairs = Tuple{RingElem,Int}[]
    sizehint!(new_pairs,length(t1.pairs)*length(t2.pairs))

    rev_dict1 = reverse_dict(t1.L.labels)
    rev_dict2 = reverse_dict(t2.L.labels)

    for p1 in t1.pairs
      c1 = p1[1]
      v1 = [ new_lex.labels[rev_dict1[i]] for i in t1.L.predicates[p1[2]]]
      for p2 in t2.pairs
        c2 = p2[1]
        v2 = [ new_lex.labels[rev_dict2[i]] for i in t2.L.predicates[p2[2]]]
        i = findfirst(x -> x==vcat(v1,v2),new_lex.predicates)
        isnothing(i) && error("Stuff went badly wrong")

        push!(new_pairs,(c1*c2,i))
      end
    end
    return Term(new_lex,new_pairs) 
end


"""
Example:

```julia
v = [1,2,3,7,4]
replacement = [10,12,13]
to_replace = 7
i = 4
_replace_number(v,i,to_replace,replacement)
```
"""



function _replace_number(v::Vector{Int}, i::Int, to_replace::Int, replacement::Vector{Int})
  new_v = Vector{Int}[]
  if v[i] == to_replace
    for r in replacement
        temp_v = copy(v)
        temp_v[i] = r
        push!(new_v,temp_v)
    end
  end

  return new_v
end

"""

Example:
```julia

L = groebner_lexicon(4,4).L

s1 = create_preimage_in(L, [[2,3,:g],["INDEX1"]], 1)
replace_with!(s1,2,"INDEX1",["1","2","g"],[1])
```
# rwel23

```julia
rwelij = create_preimage_in(L,[[:INDEX_K],[2],[:INDEX_J],[3,:g]],1)


```
"""
function replace_with!(
  t::Term,
  i::Int,
  letter::String,
  replacement::Vector{String}, 
  filter::Vector{Int}=Int[])
  L = t.L
  @assert haskey(L.labels,letter)
  letter_index = L.labels[letter]
  g_index = L.labels["g"]
  new_pairs = typeof(t.pairs)()
  replacement = Int[L.labels[x] for x in replacement]
  for p in t.pairs
    pred = L.predicates[p[2]]
    if length(pred) >= i && pred[i] == letter_index
      new_preds = _replace_number(pred,i,letter_index,replacement)
      for f in filter
        new_preds = filter_index(new_preds,i,f,g_index,L.labels["g⩓≠i$(f)"])
      end
      for new_pred in new_preds
        j = findfirst(x->x==new_pred,L.predicates)
        push!(new_pairs,(p[1],j))
      end
    else
      push!(new_pairs,p)
    end
  end
  t.pairs = new_pairs
  return t
end

function replace_with!(
  t::Term,
  letter::String,
  replacement::Vector{String}, 
  filter::Vector{Tuple{Int,Int}}=Tuple{Int,Int}[])
  n = maximum([length(t.L.predicates[p[2]]) for p in t.pairs])

  for i in 1:n
    filter_1 = [x[2] for x in filter if x[1] == i]
    t=replace_with!(t,i,letter,replacement,filter_1)
  end

  return t
end

function _get_permutations(v::Vector)
  length(v) == 1 && return [v] 
  [vcat(v[i], p) for i in 1:length(v) for p in _get_permutations(vcat(v[1:i-1],v[i+1:end]))]
end

function _get_subsets(A::Vector, n::Int)
    n == 0 && return [[]]
    [vcat(A[i], subset) for i in 1:length(A) for subset in _get_subsets(A, n-1)]
end

#=

L = groebner_lexicon(4,4).L

s1 = create_preimage_in(L, [[2,3,:g],["INDEX1"]], 1)
replace_with!(s1,2,"INDEX1",["1","2","g"],[(2,1)])
filter_index!(s1,2,1)
=#

function filter_index(v::Vector{Vector{Int}},
  i::Int,
  target::Int,
  g_index::Int,
  g_filter::Int)
  @assert target < i "You can only filter with smaller index"
  new_pairs = Vector{Int}[]
  #sizehint!(new_pairs,length(t.pairs))
  for pred in v
    if pred[i] != g_index
      pred[i] == pred[target] && continue
      push!(new_pairs,pred)
    elseif pred[target] != g_index
      push!(new_pairs,pred)
    else
      new_pred = copy(pred)
      new_pred[i] = g_filter
      push!(new_pairs,new_pred)
    end
  end
  return new_pairs
end






#= Example usage:
v = [[1], [2], [3], [:g]]

=#

#=
Example rwel

L = groebner_lexicon(4,4).L

rweljk = create_preimage_in(L,[[2],[:INDEX1],[3,:g],[:INDEX2]],1)
rweljk += create_preimage_in(L,[[3,:g],[:INDEX1],[1],[:INDEX2]],-1)
rweljk += create_preimage_in(L,[[1],[:INDEX2]],1)
rweljk += create_preimage_in(L,[[2],[:INDEX1]],-1)

# Now replace :INDEX_J with [2,3,:g]

replace_with!(rweljk,"INDEX1",["2","3","g"])
replace_with!(rweljk,"INDEX2",["2","3","g"])

=#
