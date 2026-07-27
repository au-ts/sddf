# How To Use

## 1. Build iperf_client image

## 2. Set up client or the server on another machine

## 3. Run image using machine queue 

Example:

``` bash
./mq.sh run -s odroidc4_1 -f ~/server.img -c 'run an iperf3' -a -d 200
 ```

## Client

Usage:
```
start [tcp|udp] <ip> [port] [dur_s] [streams] [bw_mbps] [len]
```

Example:
```
start tcp 172.16.0.101 5202 10 1 1000 bidirectional
```

## Server

Usage:
```
server : start server [port]
```

Example:
```
start server 5202
```

## Support

- Single Core Client: omit, multiple streams, reverse, bidrectional, target bitrate, TCP and UDP tests

- Server: TCP forward direction

