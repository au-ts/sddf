load "imgs/style.inc"

set output "imgs/s-camkes-linux.eps"

#set size 1.95,1.6

f_c_old = "data/camkes-orig.csv"
f_c_new = "data/camkes-new.csv"
f_l	= "data/linux.csv"
f_s_2p  = "data/sddf-2pd.csv"

plot f_c_old using 1:2	      lt 1 title "orig CAmkES Xput", \
     f_c_old using 1:3 	      lt 2 title "orig CAmkES CPU" axes x1y2, \
     f_c_new using 1:2	      lt 3 title "new CAmkES Xput", \
     f_c_new using 1:($3*100) lt 4 title "new CAmkES CPU" axes x1y2, \
     f_l     using 1:2	      lt 5 title "Linux Xput", \
     f_l     using 1:($3*100) lt 6 title "Linux CPU" axes x1y2, \
     f_s_2p  using 1:2	      lt 7 title "sDDF Xput", \
     f_s_2p  using 1:($3*100) lt 8 title "sDDF CPU" axes x1y2

# Reduced plot for talks: 
set output "imgs/s-linux-xput.eps"
plot f_l     using 1:2	      lt 5 title "Linux Xput", \
     f_s_2p  using 1:2	      lt 7 title "Lions Xput"

set output "imgs/s-linux.eps"
plot f_l     using 1:2	      lt 5 title "Linux Xput", \
     f_l     using 1:($3*100) lt 6 title "Linux CPU" axes x1y2, \
     f_s_2p  using 1:2	      lt 7 title "Lions Xput", \
     f_s_2p  using 1:($3*100) lt 8 title "Lions CPU" axes x1y2
