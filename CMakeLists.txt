cmake_minimum_required(VERSION 3.17)
project(edusat_project_raniadev)

set(CMAKE_CXX_STANDARD 14)

include_directories(.)


add_executable(edusat
        edusat.cpp
        edusat.h
        options.cpp
        options.h)