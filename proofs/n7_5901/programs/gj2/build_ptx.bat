@echo off
rem usage: build_ptx.bat SRC.cu OUT.ptx LL [BT] [NR] [FC] [DEFINE]  (CUDA 13.4 + MSVC build tools; LL = row length = symbols - 1,
rem BT = threads per block (128), NR = rows scanned per step at most (2), FC = frames in shared memory (0))
call "C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\VC\Auxiliary\Build\vcvars64.bat" >nul
set BTV=%4
if "%BTV%"=="" set BTV=128
set NRV=%5
if "%NRV%"=="" set NRV=2
set FCV=%6
if "%FCV%"=="" set FCV=0
set XD=%7
if "%XD%"=="" set XD=NOXD
"C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.4\bin\nvcc.exe" -arch=sm_120 -ptx -DLL=%3 -DBT=%BTV% -DNR=%NRV% -DFC=%FCV% -D%XD% -o %2 %1
echo nvcc exit %errorlevel%
