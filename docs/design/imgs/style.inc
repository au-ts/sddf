# Common definitions for plots
set datafile separator ','

# Styles
set terminal postscript eps enhanced color font "Helvetica" 12
set border linewidth 1.5

set style line 1  lw 2 lt 10 pt 3  lc rgb "red"
set style line 2  lw 2 lt 12 pt 4  lc rgb "blue"
set style line 3  lw 2 lt 12 pt 6  lc rgb "black"
set style line 4  lw 2 lt 10 pt 7  lc rgb "#006400"
set style line 5  lw 2 lt 10 pt 8  lc rgb "purple"
set style line 6  lw 2 lt 10 pt 7  lc rgb "blue"
set style line 7  lw 2 lt 10 pt 6  lc rgb "blue"
set style line 8  lw 2 lt 10 pt 7  lc rgb "blue"
set style line 9  lw 2 lt 10 pt 15 lc rgb "red"
set style line 10 lw 2 lt 10 pt 15 lc rgb "red"

set linetype 1  lw 2 pt 3 dt 1 lc rgb "red"	# orig C Xput
set linetype 2  lw 2 pt 3 dt 2 lc rgb "red"	# orig C CPU
set linetype 3  lw 2 pt 3 dt 1 lc rgb "orange"	# new C Xput
set linetype 4  lw 2 pt 3 dt 2 lc rgb "orange"	# new C CPU
set linetype 5  lw 2 pt 3 dt 1 lc rgb "#FABD05"	# Linux Xput
set linetype 6  lw 2 pt 3 dt 2 lc rgb "#FABD05"	# Linux CPU
set linetype 5  lw 2 pt 3 dt 1 lc rgb "blue"	# Linux Xput
set linetype 6  lw 2 pt 3 dt 2 lc rgb "blue"	# Linux CPU
set linetype 7  lw 2 pt 3 dt 1 lc rgb "#96CA50"	# sDDF Xput
set linetype 8  lw 2 pt 3 dt 2 lc rgb "#96CA50"	# sDDF CPU
set linetype 9  lw 2 pt 3 dt 1 lc rgb "#668B37"	# sDDF Xput alt
set linetype 10 lw 2 pt 3 dt 2 lc rgb "#668B37"	# sDDF CPU  alt

set grid noxtics noytics
set size 0.75,0.5
set style data linespoints

#set key top left vertical maxrows 4 maxcols 1
set key outside top center horizontal maxrows 2 offset 0,0.4
set xrange [0:1000]
set xlabel "Applied Load (Mb/s)"
set ylabel "Achieved Throughput (Mb/s)"
set yrange [0:1000]
set y2range [0:100]
set y2label "CPU utilisation (%)"
set ytics nomirror
set y2tics

# Data parameters
#arm_clk = 996
#x86_clk = 3400
