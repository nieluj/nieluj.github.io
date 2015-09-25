#!/bin/sh
for png in `find $1 -iname "*.png"`;
do
	echo "crushing $png"	
	pngcrush -reduce -brute "$png" temp.png
	mv -f temp.png $png
done;
