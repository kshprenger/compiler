container build --file ./Dockerfile --tag compiler-image --arch amd64 &&\
container run --arch amd64 -it -v "$(pwd)":/root/compiler -p 37080:37080 compiler-image
