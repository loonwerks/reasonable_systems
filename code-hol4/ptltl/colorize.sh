#!/bin/sh

printf "> "
while read line
do

  trim=$(echo $line | cut -c 3-)

  if [ "$trim" = "ACCEPTED" ] ; then
      echo "\033[32m$trim\033[0m"
  fi
  
  if [ "$trim" = "REJECTED" ] ; then
      echo "\033[31m$trim\033[0m"
  fi

  printf "> "
done < "${1:-/dev/stdin}"
