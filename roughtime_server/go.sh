#!/bin/sh

gcc -o server server.c message.c -I.
gcc -o client client.c message.c -I.


