@echo off

REM Windows x64
set GOOS=windows
set GOARCH=amd64
set GOARM=
set CGO_ENABLED=0
go build -ldflags="-s -w" -o ech-workers.exe ech-workers.go

REM Linux ARMv7
set GOOS=linux
set GOARCH=arm
set GOARM=7
set CGO_ENABLED=0
go build -ldflags="-s -w" -o ech-workers ech-workers.go
