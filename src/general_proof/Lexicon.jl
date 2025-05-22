#Defines the Lexicon struct

export Lexicon,
  lexicon,
  unified_lexicon,
  groebner_lexicon


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
@code_warntype lexicon([[1],[2],[3],["g"]])
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

function unified_lexicon(predicates::Vector,deg::Int,only_even::Bool=true)

  L = lexicon(predicates)
  new_preds=Vector{Int}[]
  A = collect(1:length(L.labels))

  for d in 1:deg
    only_even && d % 2 != 0 && continue
    append!(new_preds,_get_subsets(A,d))
  end
  L.predicates = new_preds
  return L
end




mutable struct GroebnerLexicon
    L::Lexicon
    lowest_generic::Int
    deg::Int
    function GroebnerLexicon(deg::Int, lowest_generic::Int, only_even::Bool)
      predicates = vcat([Int[x] for x in 1:(lowest_generic-1)],[[:g]])
      for d in 1:deg
        push!(predicates,["g⩓≠i$(d)"])
        push!(predicates,["INDEX$(d)"])
      end
      L = unified_lexicon(predicates,deg,only_even)
      return new(L,lowest_generic,deg)
    end
end

"""
  groebner_lexicon(deg::Int, lowest_generic::Int, only_even::Bool) 

```julia
groebner_lexicon(4,4)
```

"""
groebner_lexicon(deg::Int, lowest_generic::Int=4, only_even::Bool=true) = GroebnerLexicon(deg,lowest_generic,only_even)

function Base.show(io::IO, l::GroebnerLexicon)
  println(io, "GroebnerLexicon of degree $(l.deg) with lowest generic $(l.lowest_generic) \non a Lexicon with $(length(l.L.predicates)) predicates.")
end


