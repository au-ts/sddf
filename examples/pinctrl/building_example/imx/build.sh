rm -rf build/* && make MICROKIT_BOARD=maaxboard && mq.sh run -s maaxboard2 -f build/loader.img -c "ABCXYZ"

# rm -rf build/* && make MICROKIT_BOARD=imx8mq_evk && mq.sh run -s imx8mq -f build/loader.img -c "ABCXYZ"

# rm -rf build/* && make MICROKIT_BOARD=imx8mm_evk && mq.sh run -s imx8mm -f build/loader.img -c "AAAAAA"