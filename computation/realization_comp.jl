using Oscar

M = load("../computation/M$(n).mrd")
c = 2


filepath = "../data/"

X = realization(M,char=c)

if !isnothing(X.realization_matrix)
  save(filepath*"realization_matrix_M$(n)_c_$(c).mrdi",X.realization_matrix)
  save(filepath*"ground_ring_M$(n)_c_$(c).mrdi",X.ground_ring)
else
  println("No realization matrix found for c=$(c)")
end


#=
M1 = load("../computation/M1.mrd")
C = filter(x -> length(x) == 3,cyclic_flats(M1))

function no_pair(a::Int, M::Matroid)
  n = length(M)
  C = filter(x -> length(x) > 0 && length(x) < n, cyclic_flats(M))
  ret = Int[]
  for e in 1:n
    Cx = filter(x -> e in x, C)
    if all(x -> !(a in x), Cx)
      push!(ret, e)
    end
  end
  return ret
end

function pair(a::Int, M::Matroid)
  n = length(M)
  C = filter(x -> length(x) > 0 && length(x) < n, cyclic_flats(M))
  ret = Int[]
  for e in 1:n
    Cx = filter(x -> e in x, C)
    if any(x -> a in x, Cx)
      push!(ret, e)
    end
  end
  return ret
end

function intersection(a::Int,b::Int,M::Matroid)
  n = length(M)
  pa = pair(a,M)
  pb = pair(b,M)

  return intersect(pa,pb)
end
=#

