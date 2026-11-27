.PHONY: all article prerequisites
all: prerequisites

article:
	lake build

prerequisites: article
	lake -d prerequisites build
