
export reverse_dict


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




