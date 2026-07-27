# How To Use

- Build image

- Set up client/server on another machine

- Run image using machine queue (e.g.  "./mq.sh run -s odroidc4_1 -f ~/server.img -c 'run an iperf3' -a -d 200")

- client : start [tcp|udp] <ip> [port] [dur_s] [streams] [bw_mbps] [len]

- example : start tcp 172.16.0.101 5202 10 1 1000 bidirectional

- server : start server [port]

- example : start server 5202


