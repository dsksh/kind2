#!/bin/bash

kind2=/usr/local/bin/kind2
kind2_old=/usr/local/bin/kind2-1.6.0

examples=(
    "examples/counter.lus"
    "examples/circular_filter.lus"
    "examples/circular_filter_var3.lus"
    "examples/circular_filter_var36.lus"
    "examples/dc_motor_control.lus" ) 

methods=( 1 2 3 )

function echo_methods {
    echo "1) proposed method"
    echo "2) compositional mode of Kind 2"
    echo "3) monolithic mode of Kind 2"
}

function echo_help_and_exit {
    echo "Usage: run.sh [options] [method] [input_file]"
    echo "Options"
    echo "  -h\t\tPrints this message"
    echo "  --help\tPrints this message"
    echo "  --timeout <int>\tWallclock time in seconds"
    echo "  -v\t\tVerbose mode"
    echo ""
    echo "Method: one of the following"
    echo_methods
    echo ""
    echo "Input file: Lustre program filename or one of the following ids"
    for i in $(seq ${#examples[@]})
    do
        echo "$i) ${examples[$((i-1))]}"
    done
    exit 0
}

myopt=

while [ $# -ge 1 ] && [ ${1:0:1} = "-" ]
do
    if [ "$1" = "-h" -o "$1" = "--help" ]; then
        echo_help_and_exit
    elif [ "$1" = "--timeout" ] && [[ "$2" =~ ^[0-9]+$ ]]; then
        myopt="$myopt --timeout $2"
        shift 2
    elif [ "$1" = "-v" ]; then
        myopt="$myopt -v"
        shift 1
    else
        echo_help_and_exit
    fi
done

# Target configuration.

target=

function target_prompt {
    local tid=0
    echo "Example Lustre programs:"
    for i in $(seq ${#examples[@]})
    do
        echo "$i) ${examples[$((i-1))]}"
    done
    while [ -z "$tid" ] || [ $tid -lt 1 ] || [ $tid -gt ${#examples[@]} ]
    do
        printf "Select the number 1-${#examples[@]}: "
        read tid
    done
    target=${examples[$((tid-1))]}
}

while [ -z "$target" ]
do
    if [ $# -lt 2 ]; then
        target_prompt
    elif [[ "$2" =~ ^[0-9]+$ ]]; then
        if [ $2 -lt 1 ] || [ $2 -gt ${#examples[@]} ]; then
            target_prompt
        else
            tid=$2
            target=${examples[$((tid-1))]}
        fi
    else
        target=$2
    fi
done

if [ ! -e $target ]; then
    echo "File $target does not exist!"
    exit 1
fi

echo "Target: " $target
echo ""

# Method configuration.

method=

function method_prompt {
    local mid=0
    echo "Methods:"
    echo_methods
    while [ -z "$mid" ] || [ $mid -lt 1 ] || [ $mid -gt ${#methods[@]} ]
    do
        printf "Select the number 1-${#methods[@]}: "
        read mid
    done
    method=${methods[$((mid-1))]}
}

while [ -z "$method" ]
do
    if [ $# -ge 1 ] && [[ "$1" =~ ^[0-9]+$ ]]; then
        if [ $1 -lt 1 ] || [ $1 -gt ${#methods[@]} ]; then
            method_prompt
        else
            mid=$1
            method=${methods[$((mid-1))]}
        fi
    else
        method_prompt
    fi
done

echo "Method: " $method
echo ""

if [ ! -e $kind2 ]; then
    echo "Command $kind2 does not exist!"
    exit 1
fi
if [ ! -e $kind2_old ]; then
    echo "Command $kind2_old does not exist!"
    exit 1
fi

if [ $method -eq 1 ]; then
    echo "Generate a decomposed program..."
    $kind2 $myopt --enable hd $target
    target_leaves="${target}.out/${target##*/}.leaves.lus"
    if [ $? -ne 0 ] || [ ! -e $target_leaves ]; then
        echo "Failed"
        exit 1
    else
        echo "Done"
        echo ""
    fi

    echo "Verify the leaf modules..."
    $kind2_old $myopt --modular true $target_leaves
    #if [ $? -ne 0 ]; then
    if [ $? -ne 20 ]; then
        echo "Failed"
        exit 1
    else
        echo "Done"
    fi

elif [ $method -eq 2 ]; then
    echo "Run a compositional process..."
    $kind2_old $myopt --compositional true --modular true $target
    #if [ $? -ne 0 ]; then
    if [ $? -ne 20 ]; then
        echo "Failed"
        exit 1
    else
        echo "Done"
    fi

elif [ $method -eq 3 ]; then
    echo "Run a monolithic process..."
    $kind2_old $myopt --timeout 60 --compositional false --modular false $target
    #if [ $? -ne 0 ]; then
    if [ $? -ne 20 ]; then
        echo "Failed"
        exit 1
    else
        echo "Done"
    fi

else
    echo "Unreachable branch!"
    exit 1
fi

exit 0