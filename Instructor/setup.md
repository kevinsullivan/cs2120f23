# CS2120 Fall 2023 Section 002 (Sullivan)

Welcome to UVa CS2120 Fall 2022. Here are the instructions for setting up your logic and proof systems for this semester. 

## Detailed installation instructions

- Update your operating system:
  - If MacOS: Be sure your OS is up-to-date (really).
  - If Windows: You must be running Windows Pro, Education, Enterprise, or 11. If you're running Windows 10, update to Windows 11.
- Install git on your computer (if you know you already have it, skip this step):
  - Windows: https://git-scm.com/download/win
  - OSX/MacOs
    - Find and run the Terminal program
    - Enter the following command in the window: xcode-select --install
    - When it asks, please go ahead with the standard install process.
- Have a GitHub account. Create one for yourself if necessary. It's free: <https://github.com/>
- Install Docker Desktop: <https://www.docker.com/products/docker-desktop>. It's free. If you already have it, update it to the current version.
- Install VSCode: <https://code.visualstudio.com/download>. It's free.
- Launch Docker Desktop and watch for it to complete its start-up procedures.
- Use GitHub to fork this repository:
  - Be logged in to your GitHub account.
  - Visit *this* repository on GitHub (which is probably where you're reading this) while logged in to your GitHub account.
  - "Fork" this repo using the *Fork* button in the upper right corner. This will create a clone (copy) of this repository under your GitHub account. 
  - Visit *your* GitHub page to confirm that you now own a clone of this repository. Click to view the repository.
  - Select the green Code button, then HTTPS, then copy the provided URL. This is the GitHub URL of your newly forked copy of the respository.
- Start up your new environment:
  - Start a *new* VSCode window.
  - Using the "extensions" tool (four squares with one out of place on the left), search for and install the *Remote Development* extension.
  - Use CTRL/CMD-SHIFT-P to bring up the VSCode command palatte.
  - Search for and select *Clone Repository in Container Volume*
  - Paste in the GitHub URL that you copied above into the input box.
  - If you're asked to choose something, select *unique repository*.
- Now wait while your environment is built. It will take a while, possibly 15 minutes or more.
- You can click the *Starting Dev Container* to see the build process if you want. Wait for the building activity to end and for your environment to "boot up" before taking any further actions. There is a status bar at the bottom of the screen that reflects build processes status and activities.
- Configure git on your new containerized operating system
  - Open a new Terminal window in VSCode
  - Issue the following commands, filling in your details as appropriate
    - git config --global user.name "Your Name Here"
    - git config --global user.email "your@email.here"
- You may now work in and exit from VSCode as you wish. VSCode will let you re-open this project when you're ready to work on it again.

You now have, up and running, a nice discrete math development environment. You're done here now!

- Acknowledgement: This work is supported in part by the National Science Foundation under grant (Award Abstract) #1909414.
- Copyright: © 2021-2023 by Kevin Sullivan
- Contact Author: Kevin Sullivan. sullivan@virginia.edu.
