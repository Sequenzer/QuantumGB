NB1 = [[10, 11, 12],
[1, 2, 12],
[1, 3, 11],
[2, 3, 10],
[13, 14, 15],
[4, 5, 15],
[4, 6, 14],
[5, 6, 13],
[16, 17, 18],
[7, 8, 18],
[7, 9, 17],
[8, 9, 16],
[10, 13, 16],
[1, 4, 16],
[1, 7, 13],
[4, 7, 10],
[11, 14, 17],
[2, 5, 17],
[2, 8, 14],
[5, 8, 11],
[3, 15, 18],
[6, 12, 18],
[9, 12, 15],
[3, 6, 9]];

PointedNB1 = [ [(x,a) for x in a] for a in NB1 ];

function ngon(n::Int, center::Tuple{Real,Real} = (0,0), radius::Real = 1.0)
  #Create koordinates of corners 
  angles = 2*pi/n * (0:n-1)
  [(center[1] + radius*cos(angle), center[2] + radius*sin(angle)) for angle in angles ]
end


