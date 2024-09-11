#!/usr/bin/env python3
import matplotlib.pyplot as plt
import sys
import re
import json

# sample expected format:

# benchmark notified start
# benchmark start
# {
# L1 i-cache misses: 0
# L1 d-cache misses: 0
# L1 i-tlb misses: 0
# L1 d-tlb misses: 0
# Instructions: 0
# Branch mispredictions: 0
# }
# Total utilisation details: 
# {
# KernelUtilisation:  6217091260
# KernelEntries:  14350230
# NumberSchedules:  6916793
# TotalUtilisation:  1797184480480
# }
# Utilisation details for PD: ETH DRIVER ( 1)
# {
# KernelUtilisation:  711817034
# KernelEntries:  2034500
# NumberSchedules:  454767
# TotalUtilisation:  7985279612
# }
# Utilisation details for PD: MUX RX ( 2)
# {
# KernelUtilisation:  332423690
# KernelEntries:  743460
# NumberSchedules:  423688
# TotalUtilisation:  1540780386
# }
# Utilisation details for PD: MUX TX ( 3)
# {
# KernelUtilisation:  2370410978
# KernelEntries:  5352127
# NumberSchedules:  2661189
# TotalUtilisation:  8767800072
# }
# Utilisation details for PD: COPIER0 ( 4)
# {
# KernelUtilisation:  101795362
# KernelEntries:  229373
# NumberSchedules:  132126
# TotalUtilisation:  6960850678
# }
# Utilisation details for PD: LWIP CLIENT0 ( 6)
# {
# KernelUtilisation:  2298058628
# KernelEntries:  5337398
# NumberSchedules:  2660437
# TotalUtilisation:  56968114920
# }
# Utilisation details for PD: ARP ( 8)
# {
# KernelUtilisation:  6162850
# KernelEntries:  14261
# NumberSchedules:  7131
# TotalUtilisation:  23896192
# }
# Utilisation details for PD: TIMER ( 9)
# {
# KernelUtilisation:  20183988
# KernelEntries:  35466
# NumberSchedules:  24966
# TotalUtilisation:  708185834
# }
colors = ['purple', 'blue', 'green', 'red', 'cyan', 'magenta', 'yellow', 'black']
throughputs = [500000000, 750000000, 1000000000, 1250000000, 1500000000, 1750000000, 2000000000, 2500000000]
file = sys.argv[1]
with open(file, "r") as f:
    
    utils = {}
    kes = {}
    scheds = {}

    for i in range(0, len(throughputs)):
        # skip garbage
        while not re.match("Total utilisation details.*", f.readline()):
            pass

        f.readline() # {
        f.readline() # KernelUtilisation
        f.readline() # KernelEntries
        f.readline() # NumberSchedules
        [_, raw_util] = f.readline().split(':') # TotalUtilisation
        tot_util = eval(raw_util)
        f.readline() # }

        title = f.readline()
        while re.match("Utilisation details for PD: .*", title):
            pd = re.findall(r'(?<=for PD: )\w+ ?\w+', title)[0]
            # print(pd)

            f.readline() # {
            f.readline() # KernelUtilisation
            [_, ke] = f.readline().split(':') # KernelEntries
            [_, sched] = f.readline().split(':') # NumberSchedules
            [_, util] = f.readline().split(':') # TotalUtilisation
            f.readline() # }

            if pd in utils:
                utils[pd].append(eval(util) / tot_util)
                kes[pd].append(eval(ke))
                scheds[pd].append(eval(sched))
            else:
                utils[pd] = [eval(util) / tot_util]
                kes[pd] = [eval(ke)]
                scheds[pd] = [eval(sched)]
            
            title = f.readline()

    #util
    color_idx = 0
    plt.figure(figsize=(8, 6))

    for key in utils: 
        plt.plot(throughputs, utils[key], color=colors[color_idx], label=key + ' CPU Util')
        color_idx += 1
    
    plt.title('Requested Throughput' + ' vs ' + 'CPU Util')
    plt.xlabel('Requested Throughput')
    plt.ylabel('CPU Util')
    plt.grid(True)
    plt.legend()

    # plt.xscale('log')  # Since Requested_Throughput values are large, log scale for x-axis
    # plt.xticks(throughputs, [f'{x:,}' for x in throughputs])
    plt.ticklabel_format(style='sci', axis='x', scilimits=(0,0))

    plt.tight_layout()
    plt.show()


    # kernel entries
    # plt.figure(figsize=(8, 6))

    # for key in kes:
    #     plt.plot(throughputs, kes[key], color=colors.pop(), label=key + ' Kernel Entries')

    # plt.title('Requested Throughput' + ' vs ' + 'Kernel Entries')
    # plt.xlabel('Requested Throughput')
    # plt.ylabel('Kernel Entries')
    # plt.grid(True)
    # plt.legend()

    # # plt.xscale('log')  # Since Requested_Throughput values are large, log scale for x-axis
    # # plt.xticks(throughputs, [f'{x:,}' for x in throughputs])
    # plt.ticklabel_format(style='sci', axis='x', scilimits=(0,0))

    # plt.tight_layout()
    # plt.show()


    # number of scheduled
    color_idx = 0
    plt.figure(figsize=(8, 6))

    for key in scheds:
        plt.plot(throughputs, scheds[key], color=colors[color_idx], label=key + ' Number Schedules')
        color_idx += 1

    plt.title('Requested Throughput' + ' vs ' + 'Number Schedules')
    plt.xlabel('Requested Throughput')
    plt.ylabel('Number Schedules')
    plt.grid(True)
    plt.legend()

    # plt.xscale('log')  # Since Requested_Throughput values are large, log scale for x-axis
    # plt.xticks(throughputs, [f'{x:,}' for x in throughputs])
    plt.ticklabel_format(style='sci', axis='x', scilimits=(0,0))

    plt.tight_layout()
    plt.show()