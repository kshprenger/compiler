container run --name compiler-container --arch amd64 --rm -it -v "$(pwd)":/root/compiler -p 37080:37080 compiler-image
