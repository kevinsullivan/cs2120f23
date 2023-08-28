# This script must be placed in the same directory as the source files
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BOOK_PATH=$SCRIPT_DIR/DMT1
SRC_PATH=$BOOK_PATH/src

process_lean () {
    local input_file_path=$1
    local output_file_path=${SRC_PATH}/${input_file_path}.md
    command="alectryon --frontend lean4+markup $input_file_path  --backend webpage -o $output_file_path"
    echo $command
    $command
}

process_other_files () {
    local input_file_path=$1
    local input_file_dir=$(dirname $input_file_path)
    local output_file_dir=${SRC_PATH}/$input_file_dir
    local output_file_path=$output_file_dir/$(basename $input_file_path)
    mkdir -p $output_file_dir && cp $input_file_path $output_file_path
}

skip_items=("DMT1/" "build_book.sh")
#mdbook build
start_directory='.'
find "$start_directory" -type f | grep -Ev "($(IFS="|"; echo "${skip_items[*]}"))" | while read -r file_path; do
    # Use parameter expansion to extract the relative path
    relative_path="${file_path#"$start_directory"/}"
    filename=$(basename $relative_path)
    extension="${filename##*.}"
    if [ $extension = 'lean' ]; then 
        process_lean $relative_path
    else
        process_other_files $relative_path
    fi
done

cd $BOOK_PATH
mdbook build
