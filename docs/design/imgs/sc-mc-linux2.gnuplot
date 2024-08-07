load "imgs/style.inc"

f_l_mc	= "data/linux-mc2.csv"
#f_s_1c  = "data/sddf-1c.csv"
f_s_1c  = "data/sddf-5pd.csv"
f_s_mc  = "data/sddf-mc.csv"

set y2range [0:200]

set output "imgs/sc-mc-linux-xput.eps"
plot f_l_mc  using 1:2	      lt  5 title "Linux MC Xput", \
     f_s_1c  using 1:2	      lt  7 title "sDDF SC Xput", \
     f_s_mc  using 1:2	      lt  9 title "sDDF MC Xput"

set output "imgs/sc-mc-linux2.eps"
plot f_l_mc  using 1:2	      lt  5 title "Linux MC Xput", \
     f_l_mc  using 1:($3*100) lt  6 title "Linux MC CPU" axes x1y2, \
     f_s_1c  using 1:2	      lt  7 title "sDDF SC Xput", \
     f_s_1c  using 1:($3*100) lt  8 title "sDDF SC CPU" axes x1y2, \
     f_s_mc  using 1:2	      lt  9 title "sDDF MC Xput", \
     f_s_mc  using 1:($3*100) lt 10 title "sDDF MC CPU" axes x1y2
