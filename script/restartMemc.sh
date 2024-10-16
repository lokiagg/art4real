#!/bin/bash

addr=$(head -1 ../memcached.conf)
port=$(awk 'NR==2{print}' ../memcached.conf)

# kill old me
ssh ${addr} -o StrictHostKeyChecking=no "cat /var/run/memcached/memcached.pid | xargs kill"

# launch memcached
ssh ${addr} -o StrictHostKeyChecking=no "memcached -u root -l ${addr} -p  ${port} -c 10000 -d -P /var/run/memcached/memcached.pid"
sleep 1

# init 
echo -e "set serverNum 0 0 1\r\n0\r\nquit\r" | nc ${addr} ${port}
echo -e "set clientNum 0 0 1\r\n0\r\nquit\r" | nc ${addr} ${port}
