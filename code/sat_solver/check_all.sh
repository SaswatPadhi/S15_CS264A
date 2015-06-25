#!/bin/zsh

tmout=${1:-10}
log=log_$tmout

echo "" >! "$log"

make
for file in `du -b ../benchmarks/sampled/*.cnf | sort -nk1 | cut -f 2`
do
  sz=`du -k $file | cut -f 1`
  echo -ne "\r                                                  \r${sz}K \t $file"
  echo "$file" >> "$log"

  res=`timeout $tmout time ./sat -c $file 2>&1`
  echo -ne "$res\n\n" >> "$log"

  if [[ "$res" == "" ]]; then
    echo -ne "\r                                                  \rT $file\n"
  elif [[ "$res" == *"UNSAT"* ]]; then
    echo -ne "\r                                                  \rF $file\n"
  fi
done
echo -ne "\r                                                  \rALL CHECKED\n"
