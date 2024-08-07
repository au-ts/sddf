load "imgs/style.inc"

set output "imgs/kernel-sc-mc.eps"

f_s_sc   = "data/sddf-5pd.csv"
f_s_scmb = "data/sddf-mb5pd.csv"
f_s_mc   = "data/sddf-1c.csv"

set y2range [0:100]

plot f_s_sc   using 1:2	       lt  3 title "SC kernel Xput", \
     f_s_sc   using 1:($3*100) lt  4 title "SC kernel CPU" axes x1y2, \
     f_s_scmb using 1:2	       lt  7 title "MB-SC kernel Xput", \
     f_s_scmb using 1:($3*100) lt 8 title "MB-SC kernel CPU" axes x1y2, \
     f_s_mc   using 1:2	       lt 9 title "MC kernel Xput", \
     f_s_mc   using 1:($3*100) lt 10 title "MC kernel CPU" axes x1y2
