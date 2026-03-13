#Bernds computation
using Oscar


function _index_number(i::Int)
  dgs = reverse(digits(i))
  return join(["₀₁₂₃₄₅₆₇₈₉"[3*d+1] for d in dgs], "") 
end

function _magic_unitary_symbols(n::Int=6)
  u = Matrix{String}(undef, n, n)
  for i in 1:n
    for j in 1:n
      if i > 9 || j > 9
        u[i, j] = "u$(_index_number(i))₋$(_index_number(j))"
      else
        u[i, j] = "u$(_index_number(i))$(_index_number(j))"
      end
    end
  end
  return u
end

function magic_unitary(n::Int=6; fancy=true)
  if fancy
    R, u = polynomial_ring(QQ, _magic_unitary_symbols(n))
  else
    R, u = polynomial_ring(QQ, :u => (1:n, 1:n))
  end
  for i in 1:n
    for j in i:n
      u[j,i] = u[i,j]
    end
  end
  return u
end

function determinant(M)
  n = size(M, 1)
  R = parent(M[1,1])
  if n == 1
    return M[1,1]
  elseif n == 2
    return M[1,1]*M[2,2] - M[1,2]*M[2,1]
  else
    det = zero(R)
    for j in 1:n
      subM = M[2:end, [1:j-1; j+1:n]]
      det += (-1)^(1+j) * M[1,j] * determinant(subM)
    end
    return det
  end
end

function random_vector(n::Int=6)
  return transpose(QQFieldElem[rand(-10:10)//rand(1:10) for _ in 1:n])
end

C = random_vector()
U = magic_unitary()
R = parent(U[1,1])
det(matrix(R,U))

sol = Matrix{typeof(U[1,1])}(undef, 6, 6)
for x in 1:6
  next_row = C * U^x
  for y in 1:6
    sol[x,y] = next_row[y]
  end
end
sol1 = matrix(R,sol)
y = det(sol1)

l = length(terms(y))
open("output.txt", "w") do io
    write(io, string(l))
end








