@echo off
rem usage: build_ptx.bat SRC.cu OUT.ptx LLV   (CUDA 13.4 + MSVC build tools, as ..\gpu\build_ptx.bat; LLV = blocks of a full
rem row = symbols - 1; the switches LEARN, RC, NR = 3 are those of the production kernel file gpu2\k\run\gk4.ptx)
call "C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\VC\Auxiliary\Build\vcvars64.bat" >nul
"C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v13.4\bin\nvcc.exe" -arch=sm_120 -ptx -DLEARN=1 -DRC=1 -DNR=3 -DLL=%3 -o %2 %1
echo nvcc exit %errorlevel%
