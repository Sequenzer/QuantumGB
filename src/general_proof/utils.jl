
export Lexicon, lexicon, Term, create_preimage_in, reverse_dict, replace_with!


function reverse_dict(d::Dict)
  Dict(v=>k for (k,v) in d)
end

function unique_eles(v::Vector{Vector{T}}) where T
  s = Set{T}()
  for x in v
    for y in x
      push!(s, y)
    end
  end
  return s
end

mutable struct Lexicon
  predicates::Vector{Vector{Int}}
  labels::Dict{String,Int}
  coefficient_ring::Ring
  function Lexicon(v::Vector{Vector{Int}}, dct::Dict{String,Int}, coeff_ring::Ring=QQ[:n][1])
    @assert all(x->length(x) == length(v[1]), v) "Not all elements in v have the same length"
    words = unique_eles(v)
    @assert all(x->haskey(reverse_dict(dct), x), words) "Not all elements in v are in the dictionary"
    new(v, dct, coeff_ring)
  end
end

function Base.show(io::IO, l::Lexicon)
  println(io, "Lexicon with $(length(l.predicates)) predicates")
end


function Base.isequal(l1::Lexicon,l2::Lexicon)
    return l1.predicates == l2.predicates && l1.labels == l2.labels && l1.coefficient_ring == l2.coefficient_ring
end

function Base.:(==)(l1::Lexicon,l2::Lexicon)
    return l1.predicates == l2.predicates && l1.labels == l2.labels && l1.coefficient_ring == l2.coefficient_ring
end

function Base.hash(l::Lexicon, h::UInt)
  return hash(l.predicates, hash(l.labels, hash(l.coefficient_ring,h)))
end


"""
  lexicon(v::Vector{Vector{Int}})

Basic constructor for a lexicon. 

Example:

```julia
L1 = lexicon([[1],[2],[3],[-4]])
L2 = lexicon([[1],[2],[3],["g"]])

```
"""
function lexicon(v::Vector{Vector{Int}}, dct::Dict{String,Int}, coeff_ring::Ring=QQ[:n][1])
  @assert all(x->length(x) == length(v[1]), v) "Not all elements in v have the same length"
  @assert all(all(x->haskey(reverse_dict(dct), x), y) for y in v) "Not all elements in v are in the dictionary"
  Lexicon(v, dct, coeff_ring)
end

function lexicon(v::Vector{Vector{Int}})
  @assert all(x->length(x) == length(v[1]), v)
  dct = Dict{String,Int}()
  # set of all integers in the lexicon
  words = unique_eles(v)
  for x in words
    if x > 0
      dct[string(x)] = x
    else
      dct["≥$(abs(x))"] = x
    end
  end
  lexicon(v, dct)
end


function lexicon(v::Vector{Vector{String}})
  @assert all(x->length(x) == length(v[1]), v)
  wrds = unique_eles(v)
  new_v = Vector{Int}[]
  dct = Dict{String,Int}()
  for (i, x) in enumerate(wrds)
    dct[x] = i
  end
  for x in v
    push!(new_v, [dct[y] for y in x])
  end
  lexicon(new_v, dct)
end

function lexicon(v::Vector{Vector})
    v = Vector{String}[string.(x) for x in v]
    lexicon(v)
end

function find(l::Lexicon, pred::Vector{Int})
  findfirst(x->x==pred, l.predicates)
end

"""
  Base.:*(l1::Lexicon, l2::Lexicon)

This function computes the cartesian product of two lexicons.

Example:
```julia
L1 = lexicon([[1],[2],[3],["g"]])
L2 = lexicon([[1],[2],["g"],[3]])

L = L1 * L2
```
"""
function Base.:*(l1::Lexicon, l2::Lexicon)
  new_rep = Dict{String,Int}()
  @assert l1.coefficient_ring == l2.coefficient_ring "Coefficient rings do not match"

  rv1 = reverse_dict(l1.labels)
  rv2 = reverse_dict(l2.labels)
  i = 1
  for (k,v) in l1.labels
    new_rep[k] = i
    i += 1
  end
  for (k,v) in l2.labels
    if !haskey(new_rep, k)
      new_rep[k] = i
      i += 1
    end
  end

  new_v = Vector{Int}[]
  for x in l1.predicates
    for y in l2.predicates
      reps_x = [new_rep[rv1[z]] for z in x]
      reps_y = [new_rep[rv2[z]] for z in y]
      push!(new_v, vcat(reps_x, reps_y))
    end
  end

  lexicon(new_v, new_rep, l1.coefficient_ring)
end

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

v = [1,2,3,7,4]
replacement = [10,12,13]
to_replace = 7
i = 4
_replace_number(v,i,to_replace,replacement)
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

L1 = lexicon([[1],[2],[3],["g"]])
L2 = lexicon([[1],[2],["g"],[4],["INDEX"]])

L = L1 * L2

s1 = create_preimage_in(L, [[2,3,:g],[:INDEX]], 1);
replace_with!(2,"INDEX",[1,2],s1)

"""

function replace_with!(i::Int, letter::String, replacement::Vector{Int},t::Term)
  L = t.L
  @assert haskey(L.labels,letter)
  letter_index = L.labels[letter]
  new_pairs = typeof(t.pairs)()
  for p in t.pairs
    pred = L.predicates[p[2]]
    if pred[i] == letter_index
      new_preds = _replace_number(pred,i,letter_index,replacement)
      for new_pred in new_preds
        i = findfirst(L.predicates,new_pred)
        push!(new_pairs,(p[1],i))
      end
    else
      push!(new_pairs,p)
    end
  end
  t.pairs = new_pairs
  return t
end




