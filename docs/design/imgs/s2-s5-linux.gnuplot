load "imgs/style.inc"

set output "imgs/s2-s5-linux.eps"

f_l	= "data/linux.csv"
f_s_2p  = "data/sddf-2pd.csv"
f_s_4p  = "data/sddf-4pd.csv"
f_s_5p  = "data/sddf-5pd.csv"
f_s_d5p = "data/sddf-d5pd.csv"

plot f_l     using 1:2        lt  5 title 'Linux Xput', \
     f_l     using 1:($3*100) lt  6 title 'Linux CPU' axes x1y2, \
     f_s_2p  using 1:2 	      lt  1 title 'sDDF 2-PD  Xput', \
     f_s_2p  using 1:($3*100) lt  2 title 'sDDF 2-PD  CPU' axes x1y2, \
     f_s_4p  using 1:2 	      lt  3 title 'sDDF 4-PD  Xput', \
     f_s_4p  using 1:($3*100) lt  4 title 'sDDF 4-PD  CPU' axes x1y2, \
     f_s_d5p using 1:2 	      lt  7 title 'sDDF p5-PD Xput', \
     f_s_d5p using 1:($3*100) lt  8 title 'sDDF p5-PD CPU' axes x1y2, \
     f_s_5p  using 1:2 	      lt  9 title 'sDDF 5-PD  Xput', \
     f_s_5p  using 1:($3*100) lt 10 title 'sDDF 5-PD  CPU' axes x1y2

# Just s5 vs Linux for talk:

set output "imgs/s5-linux-xput.eps"
plot f_l     using 1:2        lt  5 title 'Linux Xput', \
     f_s_5p  using 1:2 	      lt  9 title 'sDDF  Xput'

set output "imgs/s5-linux.eps"
plot f_l     using 1:2        lt  5 title 'Linux Xput', \
     f_l     using 1:($3*100) lt  6 title 'Linux CPU' axes x1y2, \
     f_s_5p  using 1:2 	      lt  9 title 'sDDF  Xput', \
     f_s_5p  using 1:($3*100) lt 10 title 'sDDF  CPU' axes x1y2

# Cycles

set output 'imgs/s2-s5-linux-cyc.eps'
set ylabel 'Cycles/packet (1000s)'
set yrange [0:30]
set y2label ''
unset y2tics

plot f_s_2p  using 1:($4/1000) lt  2 title 'sDDF 2-PD', \
     f_s_4p  using 1:($4/1000) lt  4 title 'sDDF 4-PD', \
     f_s_d5p using 1:($4/1000) lt  8 title 'sDDF p5-PD', \
     f_s_5p  using 1:($4/1000) lt 10 title 'sDDF 5-PD'
